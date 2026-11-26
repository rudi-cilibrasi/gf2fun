"""Check the prime-degree generation bounds and two smooth sparse-root identities."""

import argparse
import csv
import json
import sys
from fractions import Fraction
from math import gcd, prod

from check_1229_frobenius_models import TABLE
from check_degree_1229 import GROUP, PRIMES
from check_factor_base import polynomial
from period_coordinate import CANDIDATES, mask_of


DEGREE = 1229
Q = 1 << 20
S = 1 << 10
SHIFTS = {
    "product": (6655, [(7, 1), (260, 1), (380, 1), (580, 1)]),
    "seroussi": (23571, [(1, 3), (11, 1), (20, 1), (33, 1), (560, 1), (600, 1)]),
}


def two_moment_margin(count, index):
    mass = 20 * count
    first = (1 + mass - Fraction(Q - mass, index - 1)) / S
    second = (1 + mass - Fraction(Q**2 - mass, index - 1)) / Q
    target = DEGREE - 2
    return 2 * first**2 + target * second - target**2


def longer_bound(count, index):
    weights = (38, 71, 92, 100, 92, 71, 38)
    mass = 20 * count + 1  # The degree-one value x belongs to this generating set.
    correlations = [sum(a*b for a, b in zip(weights, weights[k:])) for k in range(len(weights))]
    return 2 * sum(Fraction(correlations[k], S**k) *
                   (1 + mass - Fraction(Q**k - mass, index - 1))
                   for k in range(1, len(weights))) / correlations[0]


def check_bounds(x, modulus):
    if 2 * DEGREE**2 > 3 * Q or 2 * 20 >= DEGREE:
        raise ArithmeticError("the prime-degree generation inequality fails")
    # A prime divisor has order 1229 for 2, so it is 1 modulo 2458.
    if gcd(GROUP, prod(2 * k * DEGREE + 1 for k in range(1, 15))) != 1 or GROUP % 36871:
        raise ArithmeticError("the trial exclusion for indices below 36871 failed")
    for index, count in ((2459, 51555), (36871, 44919)):
        if not two_moment_margin(count, index) > 0 >= two_moment_margin(count - 1, index):
            raise ArithmeticError("the two-moment threshold failed")
    if any(x.pow_mod(GROUP // p, modulus) == 1 for p in PRIMES):
        raise ArithmeticError("the model coordinate misses a known prime projection")
    index = 818085338814611458
    if not longer_bound(33977, index) > DEGREE - 2 >= longer_bound(33976, index):
        raise ArithmeticError("the longer moment check failed")


def check_shift(family, model, x, modulus):
    root = polynomial(int(model["sparse_root_hex"][family], 16))
    sparse = polynomial((1 << DEGREE) + 1 + sum(1 << i for i in CANDIDATES[family]))
    if sparse.compose_mod(root, modulus):
        raise ArithmeticError("the stored sparse root fails its defining equation")
    shift, expected = SHIFTS[family]
    representative = root * x.pow_mod(shift, modulus) % modulus
    unit, factors = representative.factor()
    factors = sorted(factors, key=lambda pair: pair[0].degree())
    if unit != 1 or [(f.degree(), e) for f, e in factors] != expected:
        raise ArithmeticError("the binary factorization differs from the certificate")
    if prod(f**e for f, e in factors) != representative:
        raise ArithmeticError("the factored sparse-root identity failed")
    return [(family, shift, hex(mask_of(f)), e, f.degree(), f.degree() // gcd(f.degree(), 20))
            for f, e in factors]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--factors", action="store_true", help="export the exact binary factors as CSV")
    args = parser.parse_args()
    model = next(m for m in json.loads(TABLE.read_text()) if m["q"] == 1024)
    modulus = polynomial(int(model["modulus_hex"], 16))
    x = polynomial(2)
    check_bounds(x, modulus)
    rows = [row for family in SHIFTS for row in check_shift(family, model, x, modulus)]
    if args.factors:
        writer = csv.writer(sys.stdout, lineterminator="\n")
        writer.writerow(("candidate", "shift", "binary_mask", "multiplicity", "binary_degree", "degree_over_F2_20"))
        writer.writerows(rows)
    else:
        print("Verified generation by any 44919 degree-20 values in every degree-1229 coordinate.")
        print("The specified coordinate and any 33977 degree-20 values generate the full group.")
        for family, (shift, _) in SHIFTS.items():
            maximum = max(row[-1] for row in rows if row[0] == family)
            print(f"{family}: x^{shift} times the sparse root has factors of degree at most "
                  f"{maximum} over F_(2^20).")
