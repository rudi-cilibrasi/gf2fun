"""Verify the genera zero and one classification in the degree-1229 Frobenius census."""

import argparse
import csv
import gzip
import io
import json
import subprocess
from collections import Counter
from pathlib import Path

from flint import fq_default_ctx, fq_default_poly_ctx, nmod_poly

from check_1229_sparse_frobenius import SUPPORTS, support_table
from check_factor_base import DATA

SIDE = 20
EXPECTED = {256: (1, 20), 512: (57, 12), 1024: (15, 14), 2048: (2, 13)}
ELLIPTIC_TAPS = (136, 683, 819)


def remainder(bits, modulus):
    degree = modulus.bit_length() - 1
    while bits.bit_length() > degree:
        bits ^= modulus << (bits.bit_length() - degree - 1)
    return bits


def check_kernel(q, taps, rows):
    """Evaluate the relation and prove that its multiples fill the square kernel."""
    f = (1 << 1229) | 1 | sum(1 << t for t in taps)
    u = max(c.bit_length() for c in rows) - 1
    v = len(rows) - 1
    if not (1 <= u <= SIDE and 1 <= v <= SIDE and rows[-1] > 0 and min(rows) >= 0):
        raise ValueError("invalid bivariate coefficients")
    pivots = {}
    value = 0
    y = 1
    for j in range(SIDE+1):
        x = y
        for i in range(SIDE+1):
            if j <= v and (rows[j] >> i) & 1:
                value ^= x
            column = x
            while column:
                # Use the lowest nonzero coefficient as pivot, independently of NTL.
                bit = column & -column
                if bit not in pivots:
                    pivots[bit] = column
                    break
                column ^= pivots[bit]
            x = remainder(x << 1, f)
        y = remainder(y << q, f)
    nullity = (SIDE+1)**2 - len(pivots)
    if value or nullity != (SIDE+1-u)*(SIDE+1-v):
        raise ArithmeticError(f"incorrect relation or kernel dimension for {q}, {taps}")
    return max(u, v)


def smooth_torus_points(rows, m):
    """Count nonzero rational y roots in each x fibre, excluding both partials zero."""
    field = fq_default_ctx(2, m)
    ring = fq_default_poly_ctx(field)
    y = ring.gen()
    q = 1 << m
    exponents = [[i for i in range(c.bit_length()) if (c >> i) & 1] for c in rows]
    u = max(c.bit_length() for c in rows) - 1
    zero = field.zero()
    count = 0
    for mask in range(1, q):
        x = field([(mask >> i) & 1 for i in range(m)])
        powers = [field.one()]
        for _ in range(u):
            powers.append(powers[-1]*x)
        f = ring([sum((powers[i] for i in terms), zero) for terms in exponents])
        if f.is_zero():
            raise ArithmeticError("unexpected vertical component")
        if f.degree() == 0:
            continue
        distinct = f.gcd(y.pow_mod(q-1, f)-1)
        if distinct.degree() > 0:
            dx = ring([sum((powers[i] for i in terms if i % 2), zero) for terms in exponents])
            count += distinct.degree() - distinct.gcd(dx).gcd(f.derivative()).degree()
    return count


def closed_places(rational, previous, m):
    points = rational - sum(d * previous[d] for d in previous if m % d == 0)
    places, remainder = divmod(points, m)
    if places < 0 or remainder:
        raise ArithmeticError("invalid closed-place count")
    return places


def elliptic_places(trace):
    """Closed places through degree eight for an elliptic curve of this trace."""
    result = {}
    previous, current = 2, trace
    for m in range(1, 9):
        result[m] = closed_places(2**m + 1 - current, result, m)
        previous, current = current, trace * current - 2 * previous
    return result


def exclude_elliptic(rows, known_degree, known_count, possibilities):
    traces = set(possibilities)
    places = {}
    for m in range(1, 9):
        points = known_count if m == known_degree else smooth_torus_points(rows, m)
        places[m] = closed_places(points, places, m)
        traces = {t for t in traces if places[m] <= possibilities[t][m]}
        if not traces:
            return
    raise ArithmeticError(f"remaining elliptic traces: {sorted(traces)}")


def elliptic_identity(rows, q):
    """Substitute X=(v/u^2)^s and Y=v^8/u into the displayed curve identically."""
    s = {1024: 2, 2048: 1}[q]
    terms = [(i, j) for j, mask in enumerate(rows)
             for i in range(mask.bit_length()) if mask >> i & 1]
    top = max(2*s*i + j for i, j in terms)
    v = nmod_poly([0, 1], 2)
    zero, one = 0*v, v**0
    # u^2 = (v^3+1)u + v^3(v+1)^2 in the quadratic function field.
    linear, constant = v**3 + 1, v**3 * (v+1)**2
    powers = [(one, zero)]
    for _ in range(top):
        a, b = powers[-1]
        powers.append((constant*b, a + linear*b))
    left, right = zero, zero
    for i, j in terms:
        a, b = powers[top - 2*s*i - j]
        coefficient = v**(s*i + 8*j)
        left += coefficient*a
        right += coefficient*b
    if left or right:
        raise ArithmeticError("elliptic functions do not satisfy the curve equation")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", type=Path, help="also recompute the full NTL scan")
    parser.add_argument("--jobs", type=int, default=1, help="threads for the full scan")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    supports = {tuple(map(int, row)) for row in support_table().T}
    archive = json.loads((DATA / "degree-1229-frobenius-curves.json").read_text())
    if archive["side"] != SIDE:
        raise ValueError("unsupported square")
    keys = []
    minima = {}
    elliptic = []
    possibilities = {trace: elliptic_places(trace) for trace in range(-2, 3)}
    for row in archive["curves"]:
        q, taps, coeffs = row["q"], tuple(row["taps"]), row["coefficients"]
        if q not in EXPECTED or taps not in supports:
            raise ValueError("unknown field or support")
        side = check_kernel(q, taps, coeffs)
        minima[q] = min(side, minima.get(q, side))
        m = row["point_degree"]
        if not 1 <= m <= 13:
            raise ValueError("unknown point-count field degree")
        count = smooth_torus_points(coeffs, m)
        if count != row["smooth_points"] or count <= (1 << m)+1:
            raise ArithmeticError(f"insufficient smooth point count for {q}, {taps}")
        if taps == ELLIPTIC_TAPS:
            elliptic_identity(coeffs, q)
            elliptic.append(q)
        else:
            exclude_elliptic(coeffs, m, count, possibilities)
        keys.append((q, *taps))
    counts = Counter(key[0] for key in keys)
    if keys != sorted(set(keys)) or {q: (counts[q], minima[q]) for q in EXPECTED} != EXPECTED:
        raise ArithmeticError("unexpected curve census")
    print(f"Verified the relations, kernel dimensions and positive genus for all {len(keys)} curves.")
    if elliptic != [1024, 2048]:
        raise ArithmeticError("unexpected elliptic models")
    print("Verified two elliptic models and excluded genus one for the other 73 curves.")
    if args.census:
        with gzip.open(SUPPORTS, "rb") as f:
            result = subprocess.run([str(args.census.resolve()), str(SIDE), str(args.jobs)],
                                    input=f.read(), stdout=subprocess.PIPE, check=True)
        reader = csv.reader(io.StringIO(result.stdout.decode("ascii")))
        if next(reader) != ["q", "a", "b", "c"] or [tuple(map(int, r)) for r in reader] != keys:
            raise ArithmeticError("the full NTL scan disagrees with the archive")
        print(f"Verified every square for {len(supports)} reciprocal representatives.")


if __name__ == "__main__":
    main()
