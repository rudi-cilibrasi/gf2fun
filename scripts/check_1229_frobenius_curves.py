"""Verify every positive-genus curve in the degree-1229 Frobenius square census."""

import argparse
import csv
import gzip
import io
import json
import subprocess
from collections import Counter
from pathlib import Path

from flint import fq_default_ctx, fq_default_poly_ctx

from check_1229_sparse_frobenius import SUPPORTS, support_table
from check_factor_base import DATA

SIDE = 20
EXPECTED = {256: (1, 20), 512: (57, 12), 1024: (15, 14), 2048: (2, 13)}


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
        keys.append((q, *taps))
    counts = Counter(key[0] for key in keys)
    if keys != sorted(set(keys)) or {q: (counts[q], minima[q]) for q in EXPECTED} != EXPECTED:
        raise ArithmeticError("unexpected curve census")
    print(f"Verified the relations, kernel dimensions and positive genus for all {len(keys)} curves.")
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
