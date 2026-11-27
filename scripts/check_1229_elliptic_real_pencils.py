"""Verify the real pencils for all 3,087 degree-130 and degree-150 elliptic factors."""

import argparse
import gzip
import json
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import cache
from math import gcd
from pathlib import Path

from flint import fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx

from check_degree_1229 import COFACTOR
from check_factor_base import DATA, irreducible, polynomial


CERTIFICATE = DATA / "degree-1229-elliptic-real-pencils.json.gz"
# The root w maps to z^1025 in the project's F_(2^20) polynomial basis.
MODULUS = [1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1]
BASE = fq_default_ctx(modulus=fmpz_mod_poly_ctx(2)(MODULUS), var="w")
RING = fq_default_poly_ctx(BASE)
T = RING.gen()
H0, H1 = T**5 + T**2 + 1, T**3 + T


@cache
def scalar(c):
    if type(c) is not int or not 0 <= c < 1024:
        raise ValueError("coefficient outside the ten-bit basis")
    return BASE([(c >> j) & 1 for j in range(c.bit_length())])


@cache
def homogeneous_powers(m):
    return [H0**j * H1**(m-j) for j in range(m+1)]


def verify_row(row):
    mask, gs, hs = row
    d = mask.bit_length()-1
    if d not in (130, 150) or not irreducible(polynomial(mask)):
        raise ValueError(f"incorrect binary parent {mask:#x}")
    t, m = d//10, d//10-1
    g, h = (RING([scalar(c) for c in values]) for values in (gs, hs))
    if max(g.degree(), h.degree()) != m or not g.gcd(h).is_one():
        raise ValueError(f"incorrect degree or common factor at {mask:#x}")

    def homogeneous(p):
        return sum((c*v for c, v in zip(p.coeffs(), homogeneous_powers(m))), RING.zero())

    numerator = homogeneous(g)*(g+h) + homogeneous(h)*g
    if numerator.is_zero():
        raise ArithmeticError(f"zero numerator at {mask:#x}")
    binary = RING([(mask >> j) & 1 for j in range(d+1)])
    multiplicity = 0
    for f, e in numerator.factor()[1]:
        k = f.degree()
        if k == t and (binary % f).is_zero():
            # Its ten coefficient conjugates multiply to the irreducible binary parent.
            multiplicity += e
        elif k//gcd(k, 2) > m:
            raise ArithmeticError(f"a different factor exceeds relative degree {m} at {mask:#x}")
    if gcd(multiplicity, COFACTOR) != 1:
        raise ArithmeticError(f"the parent multiplicity is not invertible at {mask:#x}")
    return d, multiplicity


def read_rows():
    with gzip.open(CERTIFICATE, "rt") as stream:
        rows = [(int(p, 16), g, h) for p, g, h in json.load(stream)]
    masks = [p for p, _, _ in rows]
    if (masks != sorted(set(masks))
            or Counter(p.bit_length()-1 for p in masks) != {130: 1029, 150: 2058}):
        raise ValueError("incomplete or repeated real pencil masks")
    return rows


def check_frontier(path, rows):
    # Output of check_1229_elliptic_descent.py --lower-seven --json.
    task = json.loads(path.read_text())
    if task["task"] != "elliptic" or len(task["remaining"]) != 4404:
        raise ValueError("expected the verified seven-input elliptic expansion")
    needed = set()
    for entry in task["remaining"]:
        p = int(entry["mask_hex"], 16)
        d = p.bit_length()-1
        if entry["relative_degree"] != d//gcd(d, 20):
            raise ValueError("incorrect relative degree in the supplied expansion")
        if d in (130, 150):
            needed.add(p)
        elif entry["relative_degree"] > 9:
            raise ValueError("unexpected large factor in the supplied expansion")
    if needed != {p for p, _, _ in rows}:
        raise ValueError("the real pencils do not cover the supplied expansion")


def expand(row):
    from check_1229_elliptic_descent import subfield_relation
    from check_1229_hermitian_descent import F, bits
    from check_1229_log_descent import reduce_task
    from check_1229_power_images import split_log_table
    from check_degree_1229 import KNOWN

    p, g, h = row
    w = F.gen()**1025
    if not sum((w**i for i, c in enumerate(MODULUS) if c), F.zero()).is_zero():
        raise ArithmeticError("incompatible embedding of the ten-bit basis")

    def lift(c):
        return bits(sum((w**i for i in range(10) if c >> i & 1), F.zero()))

    form = {"coefficient_degree": 10, "height": (p.bit_length()-1)//10-1,
            "g": list(map(lift, g)), "h": list(map(lift, h))}
    field_mask, table = split_log_table()
    field = polynomial(field_mask)
    terms = subfield_relation(p, form, field)
    return reduce_task(hex(p), polynomial(p), terms, table,
                       polynomial(2).pow_mod(KNOWN, field), field, None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontier", type=Path, help="match the complete verified --lower-seven JSON output")
    parser.add_argument("--expand", type=lambda s: int(s, 0), metavar="MASK",
                        help="export and power-check the full projected logarithm equation for one parent")
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    rows = read_rows()
    if args.frontier:
        check_frontier(args.frontier, rows)
    if args.expand is not None:
        row = next((row for row in rows if row[0] == args.expand), None)
        if row is None:
            parser.error("choose a degree-130 or degree-150 mask in the seven-input expansion")
        verify_row(row)
        print(json.dumps(expand(row), indent=2))
        return
    if args.jobs == 1:
        counts = Counter(map(verify_row, rows))
    else:
        with ProcessPoolExecutor(max_workers=args.jobs) as pool:
            counts = Counter(pool.map(verify_row, rows, chunksize=16))
    for d in (130, 150):
        n = sum(v for (degree, _), v in counts.items() if degree == d)
        print(f"{n:,} degree-{d} parents reduce to relative degree at most {d//10-1}.")


if __name__ == "__main__":
    main()
