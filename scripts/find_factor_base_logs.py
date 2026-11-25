"""Collect binary polynomial relations and recover directly checkable powers of X."""

import argparse
import csv
from functools import lru_cache
from math import gcd as integer_gcd
import sys

from check_factor_base import irreducible, irreducible_counts, modulus, polynomial
from make_witnesses import gcd, mask_product


@lru_cache(maxsize=32768)
def factor(mask):
    return {sum(int(c) << i for i, c in enumerate(p)): e for p, e in polynomial(mask).factor()[1]}


def frobenius(mask, q):
    return sum(1 << (i*q) for i in range(mask.bit_length()) if mask & (1 << i))


def insert(row, pivots, order, *, fixed_x=True):
    """Insert a unit pivot. With fixed_x, the column for X has known logarithm 1."""
    row = {p: c % order for p, c in row.items() if c % order}
    while row:
        p = max(row)
        c = row[p]
        if fixed_x and p == 2:
            raise ValueError(f"the relations give the proper order multiple {c} for X")
        if p not in pivots:
            if integer_gcd(c, order) == 1:
                inv = pow(c, -1, order)
                pivots[p] = {k: (t * inv) % order for k, t in row.items()}
                return True
            return False
        for k, t in pivots[p].items():
            value = (row.get(k, 0) - c*t) % order
            if value:
                row[k] = value
            else:
                row.pop(k, None)
    return False


def recover(pivots, order):
    logs = {2: 1}
    for p, row in sorted(pivots.items()):
        if all(k == p or k in logs for k in row):
            logs[p] = -sum(c * logs[k] for k, c in row.items() if k != p) % order
    return logs


def relations(n, tail, degree, bound, radius):
    for q in (4, 8, 16, 2, 32):
        shifts = range(max(1, n//q-radius), (n+q-1)//q+radius+1)
        for h in sorted(shifts, key=lambda j: abs(j*q-n)):
            offset = h*q - n
            for a in range(1, 1 << (degree+1)):
                for b in range(1, 1 << (degree+1)):
                    if max(a.bit_length(), b.bit_length()) != degree+1 or gcd(a, b) != 1:
                        continue
                    u = (a << h) ^ b
                    if not u:
                        continue
                    left = factor(u)
                    if any(p.bit_length() > bound+1 for p in left):
                        continue
                    g = mask_product(tail, frobenius(a, q))
                    v = (g << max(offset, 0)) ^ (frobenius(b, q) << max(-offset, 0))
                    right = factor(v)
                    if any(p.bit_length() > bound+1 for p in right):
                        continue
                    # X^max(-offset,0) U^q = V in the field.
                    row = right.copy()
                    for p, e in left.items():
                        row[p] = row.get(p, 0) - q*e
                    row[2] = row.get(2, 0) - max(-offset, 0)
                    yield row


def search(n, taps, bound, pair_degree, radius, output_degree):
    f = modulus(n, taps)
    if not irreducible(f):
        raise ValueError("the field modulus is reducible")
    order = (1 << n) - 1
    tail = 1 + sum(1 << i for i in taps)
    needed = sum(irreducible_counts(bound).values()) - 1
    wanted = sum(irreducible_counts(output_degree).values())
    pivots = {}
    count = 0
    for degree in range(1, pair_degree+1):
        for row in relations(n, tail, degree, bound, radius):
            insert(row, pivots, order)
            count += 1
            if len(pivots) == needed:
                break
        logs = {p: e for p, e in recover(pivots, order).items() if p.bit_length() <= output_degree+1}
        print(f"Pair degree {degree}, {count} relations, {len(pivots)} pivots, "
              f"{len(logs)} of {wanted} requested logarithms.", file=sys.stderr)
        if len(logs) == wanted:
            break
    x = polynomial(2)
    if any(x.pow_mod(e, f) != polynomial(p) for p, e in logs.items()):
        raise ArithmeticError("a recovered value failed direct exponentiation")
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(("mask", "exponent"))
    writer.writerows(sorted(logs.items()))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", type=int)
    parser.add_argument("--taps", nargs=3, type=int, required=True, metavar=("A", "B", "C"))
    parser.add_argument("--factor-degree", required=True, type=int)
    parser.add_argument("--pair-degree", default=6, type=int)
    parser.add_argument("--shift-radius", default=0, type=int)
    parser.add_argument("--output-degree", type=int, help="keep logs through this degree")
    args = parser.parse_args()
    if not 0 < args.taps[0] < args.taps[1] < args.taps[2] < args.degree:
        parser.error("expected three increasing interior exponents")
    output_degree = args.factor_degree if args.output_degree is None else args.output_degree
    if not 1 <= output_degree <= args.factor_degree < args.degree or args.pair_degree < 1 or args.shift_radius < 0:
        parser.error("invalid degree or shift bounds")
    search(args.degree, args.taps, args.factor_degree, args.pair_degree, args.shift_radius, output_degree)
