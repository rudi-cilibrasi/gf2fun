"""Verify how early a missing cofactor prime forces a product of conjugates to equal one."""

import argparse
import json
from fractions import Fraction
from math import gcd, prod

from flint import fmpz, fmpz_mod_poly_ctx

from check_1229_wheel import EXTENDED_BOUND
from check_degree_1229 import COFACTOR, N
from check_factor_base import DATA


def frequency_products(n, cofactor, odd, bound, residue):
    c = fmpz(cofactor)
    frequencies = [pow(fmpz(t), n, c) for t in odd]
    product = fmpz(1)
    for j, v in enumerate(frequencies):
        for u in frequencies[:j]:
            product = product * (v-u) % c
    if product.gcd(c) != 1:
        raise ArithmeticError(f"positive frequency coincidence, gcd {product.gcd(c)}")
    ring = fmpz_mod_poly_ctx(c)
    polynomial = ring.one()
    for v in frequencies:
        polynomial *= ring([v, 1])
    # P(b^n) checks every possible negative frequency from this odd b.
    batch = 2048
    product = fmpz(1)
    for low in range(1, bound, 2*batch):
        values = [pow(fmpz(b), n, c) for b in range(low, min(low+2*batch, bound), 2)]
        for value in polynomial.multipoint_evaluate(values):
            product = product * int(value) % c
    if product != residue or gcd(residue, cofactor) != 1:
        raise ArithmeticError(f"negative-frequency product differs or has gcd {product.gcd(c)}")
    return len(odd)*(bound//2)


def moment(n, least_prime, odd, bound, target):
    a = sum(Fraction(1, t*t) for t in odd)
    v = sum(Fraction(1, t) for t in odd)
    # pi < 3.1416 and the error in each cotangent main term is at most pi*t/(4*ell^2).
    lower = Fraction(2500, 3927)*(a - Fraction(n-1, bound)*v) - Fraction(4*len(odd), least_prime**2)
    score = 2*n*lower**2/a
    if lower <= 0 or score <= target:
        raise ArithmeticError("insufficient second moment")
    counts = {}
    for imbalance in (35, 33):
        # Each sign pair contributes one lighter word.
        count = (least_prime-1)*(target-imbalance**2) // (2*(n**2-imbalance**2))
        counts[(n-imbalance-2)//2] = count
    return score, counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true", help="include the five further open degrees through 1280")
    args = parser.parse_args()
    archive = json.loads((DATA/"exterior-failure-frequency-products.json").read_text())
    params = {N: (COFACTOR, EXTENDED_BOUND+1)}
    for row in json.loads((DATA/"open-degrees-1231-1259.json").read_text()):
        n, c = row["degree"], row["cofactor"]
        if c*prod(row["known_prime_factors"]) != (1 << n)-1:
            raise ValueError("incorrect cofactor in the order table")
        params[n] = (c, 2 + 2*n*(1 << (2*row["log_block"])))
    if set(params) != {1229, 1231, 1237, 1243, 1249, 1259} or set(map(int, archive)) != set(params):
        raise ValueError("incomplete list of degrees")
    for n in (sorted(params) if args.all else [N]):
        c, least = params[n]
        for p, _ in fmpz(n).factor():
            if gcd((1 << (n//int(p)))-1, c) != 1:
                raise ArithmeticError("a cofactor prime has smaller dyadic order")
        row = archive[str(n)]
        bound, last = row["bound"], row["last_odd"]
        if not 0 < last < bound < least or last % 2 != 1 or bound % 2:
            raise ValueError("invalid frequency range")
        odd = range(1, last+1, 2)
        checked = frequency_products(n, c, odd, bound, row["residue"])
        score, counts = moment(n, least, odd, bound, 1226 if n == N else 1225)
        print(f"Degree {n}, {checked:,} negative-frequency exclusions, "
              f"second-moment lower bound {float(score):.4f} (rounded).")
        print(f"If a cofactor prime is missing, the first failing rank is at most {(n-37)//2}.")
        if n == N:
            if counts[596] < 270_000_000_000 or counts[597] < 37_000_000_000_000:
                raise ArithmeticError("insufficient number of light words")
            for rank, count in counts.items():
                print(f"More than {count:,} distinct product-one selections have rank at most {rank}.")


if __name__ == "__main__":
    main()
