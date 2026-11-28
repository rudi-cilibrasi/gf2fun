"""Replay the support codes for simultaneous monomial substitutions."""

import csv
import gzip
from collections import Counter
from itertools import combinations
from math import comb

from flint import fmpz

from check_degree_1229 import GROUP, KNOWN, N, PRIMES
from check_factor_base import DATA, irreducible, modulus, polynomial
from make_witnesses import gcd as polynomial_gcd, x_power


def rank_bits(count):
    return (count - 1).bit_length()


def check_degree_1229():
    with gzip.open(DATA / "degree-1229-irreducible-supports.csv.gz", "rt", newline="") as stream:
        masks = Counter(int(row["missing_mask"]) for row in csv.DictReader(stream))
    if masks != {0: 319572, 1: 5, 2: 6}:
        raise ArithmeticError(f"unexpected reciprocal-pair census {masks}")
    if any(not fmpz(q).is_prime() or GROUP % q or (q - 1) % N for q in PRIMES):
        raise ArithmeticError("incorrect prime in the base field order")
    for size in range(1, len(PRIMES) + 1):
        for indices in combinations(range(len(PRIMES)), size):
            mask = sum(1 << i for i in indices)
            count = 2 * sum(c for failed, c in masks.items() if not (failed & mask))
            expected = 639166 - 10 * (0 in indices) - 12 * (1 in indices)
            if count != expected or rank_bits(count) != 20:
                raise ArithmeticError(f"incorrect code size for {indices}")
    for name, m, expected in (("36871*46703", PRIMES[0]*PRIMES[1], 121),
                              ("the four-prime product", KNOWN, 888),
                              ("the full field order", GROUP, 3716)):
        bits = rank_bits(comb(N*m - 1, 3))
        if bits != expected:
            raise ArithmeticError(f"unexpected tap rank length for {name}")
        print(f"At multiplier {name}, an unrestricted tap rank takes {bits} bits.")
    print("Verified all fifteen nonempty choices of known base primes.")


def check_degree_eleven():
    p = 11
    group = 2**p - 1
    x = polynomial(2)
    counts = Counter()
    for interior in (1, 3):
        for taps in combinations(range(1, p), interior):
            # Check the two reciprocal orientations separately.
            base = modulus(p, taps)
            if not irreducible(base):
                continue
            base_order = next(d for d in (23, 89, group) if x.pow_mod(d, base) == 1)
            for m in (23*89, 23**2*89):
                # Quotient-ring powers test the actual large polynomial.
                expanded = sum(1 << (m*k) for k in (0, *taps, p))
                order = m*base_order
                if x_power(order, expanded) != 1:
                    raise ArithmeticError("a root does not have the predicted annihilating power")
                if base_order == group:
                    if any(polynomial_gcd(x_power(order//q, expanded) ^ 1, expanded) != 1
                           for q in (23, 89)):
                        raise ArithmeticError("a root misses a prime of the predicted order")
                    n = p*m
                    if pow(2, n, order) != 1 or any(pow(2, n//q, order) == 1 for q in (p, 23, 89)):
                        raise ArithmeticError("the predicted order has the wrong binary degree")
                else:
                    # The short Frobenius period gives a proper factor or a proper subfield.
                    if pow(2, p*m, order) != 1 or all(
                        pow(2, p*m//q, order) != 1 for q in (p, 23, 89)
                    ):
                        raise ArithmeticError("an imprimitive base could have an irreducible expansion")
            counts[interior, base_order] += 1
    if counts != {(1, group): 2, (3, 89): 2, (3, group): 44}:
        raise ArithmeticError(f"incorrect degree-eleven base counts {counts}")
    print(f"Degree-eleven oriented base counts by (interior taps, order): {dict(sorted(counts.items()))}")
    return counts


if __name__ == "__main__":
    check_degree_1229()
    check_degree_eleven()
