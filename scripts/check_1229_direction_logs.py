"""Recover projected logarithms from affine lines in three binary projective coordinates."""

import argparse
import csv
from collections import Counter, defaultdict
from math import gcd
from pathlib import Path

import numpy as np

from check_1229_circle_relations import homogeneous
from check_1229_factor_base_orders import extended_table, read_logs, read_table
from check_1229_isogeny_logs import H0, H1, Q
from check_1229_partial_circles import binary_orbits
from check_1229_translated_circles import Constants, SIZE
from check_degree_1229 import COFACTOR, GROUP, KNOWN, PRIMES
from check_factor_base import DATA, polynomial
from period_coordinate import mask_of


LOGS = DATA / "degree-1229-direction-logs.csv"
CHARTS = ((2, 1), (3, 1), (3, 2))


def factors(value):
    return {mask_of(p): int(e) for p, e in value.factor()[1]}


def linear(mask, u, v):
    return (u if mask & 2 else 0*u) + (v if mask & 1 else 0*v)


def equations(table):
    field = Constants()
    reps, masks = binary_orbits(field, table)
    directions = {int(masks[field.rep[z]]) for z in field.power[field.torus_exponents]}
    inverse_q = pow(Q, -1, COFACTOR)
    for f, g in CHARTS:
        # Regular, nonzero values of the chart on the finite binary orbits.
        a = (reps if f & 2 else 0*reps) ^ (f & 1)
        b = (reps if g & 2 else 0*reps) ^ (g & 1)
        regular = (a != 0) & (b != 0)
        power = (field.log[a[regular]] - field.log[b[regular]]).astype(np.int64)
        images = field.power[((Q-1)*power) % (SIZE-1)]
        source = defaultdict(int)
        degrees = Counter()
        for p, label, degree in zip(masks[reps[regular]], masks[field.rep[images]],
                                    field.degree[reps[regular]], strict=True):
            source[int(label)] += table[int(p)]
            degrees[int(label)] += int(degree)
        if source.keys() != directions:
            raise ArithmeticError("the chart missed a direction")

        # At y=x^q this ratio equals phi(x)^(q-1).
        u = polynomial(f) * linear(g, H0, H1)
        v = polynomial(g) * linear(f, H0, H1)
        common = u.gcd(v)
        u, v = u // common, v // common
        denominator_log = sum(e*table[p] for p, e in factors(v).items())
        pole_log = table[g] if g != 1 else 0
        for label in sorted(directions):
            d = label.bit_length()-1
            # The fiber over one also contains infinity when phi(infinity)=1.
            infinity = int(f >= 2 and g >= 2 and label == 3)
            if degrees[label] + infinity != (Q-1)*d:
                raise ArithmeticError("incorrect total degree of the direction fiber")
            numerator = homogeneous(polynomial(label), u, v)
            rhs = (inverse_q*(source[label] - d*(Q-1)*pole_log) + d*denominator_log) % COFACTOR
            yield rhs, factors(numerator)


def derive(original, known):
    pending = list(equations(original))
    count = len(pending)
    added = {}
    while True:
        deferred = []
        for rhs, terms in pending:
            missing = [p for p in terms if p not in known and p not in added]
            if len(missing) > 1:
                deferred.append((rhs, terms))
                continue
            offset = sum(e*(known[p] if p in known else added[p])
                         for p, e in terms.items() if p in known or p in added)
            if missing:
                p, = missing
                added[p] = (rhs-offset)*pow(terms[p], -1, COFACTOR) % COFACTOR
            elif (rhs-offset) % COFACTOR:
                raise ArithmeticError("inconsistent projected logarithm")
        if len(deferred) == len(pending):
            return count, added
        pending = deferred


def check_cubic(table, logs):
    t = polynomial(2)
    phi5 = polynomial(31)
    target = homogeneous(phi5, t*H1, H0)
    if factors(target) != {0x13: 1, 0x19: 1, 0x154b: 1}:
        raise ArithmeticError("incorrect factorization of the fifth-root direction")
    source = factors(phi5(t**(Q-1)))
    degrees = Counter(p.bit_length()-1 for p in source)
    if degrees != {4: 3, 20: 204} or any(e != 1 for e in source.values()):
        raise ArithmeticError("incorrect source factorization of the fifth-root direction")
    total = sum(table[p] for p in source)
    exponent = pow(Q, -1, COFACTOR)*total + 4*table[mask_of(H0)] - table[0x13] - table[0x19]
    if exponent % COFACTOR != logs[0x154b]:
        raise ArithmeticError("the explicit cubic identity disagrees with the orbit computation")


def check_orders(modulus, logs):
    field = polynomial(modulus)
    base = polynomial(2).pow_mod(KNOWN, field)
    for p, exponent in logs.items():
        value = polynomial(p)
        if gcd(exponent, COFACTOR) != 1 or base.pow_mod(exponent, field) != value.pow_mod(KNOWN, field):
            raise ArithmeticError(f"failed cofactor order certificate for {p:#x}")
        if any(value.pow_mod(GROUP//prime, field) == 1 for prime in PRIMES):
            raise ArithmeticError(f"missing a prime-order component for {p:#x}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export", type=Path, help="write the regenerated mask,exponent CSV")
    parser.add_argument("--orders", action="store_true", help="verify every full order directly with FLINT")
    args = parser.parse_args()
    modulus, original = read_table()
    count, extra = derive(original, extended_table(original))
    check_cubic(original, extra)
    rows = sorted(extra.items())
    if args.export:
        with args.export.open("w", newline="") as stream:
            writer = csv.writer(stream, lineterminator="\n")
            writer.writerow(("mask", "exponent"))
            writer.writerows(rows)
    elif rows != list(read_logs(LOGS)):
        raise ArithmeticError("regenerated exponents differ from the published table")
    print(f"{count} direction equations determine {len(rows)} logarithms outside the starting table.")
    print("Binary degrees and counts:", dict(sorted(Counter(p.bit_length()-1 for p in extra).items())))
    if args.orders:
        check_orders(modulus, extra)
        print(f"Verified all {len(rows)} primitive elements by direct field powering.")
