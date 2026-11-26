"""Compute logarithms of exact Frobenius-order factors and count reduced fractions at an Ore root.

Run with python-flint and sympy. Seed and polynomial masks use bit i for X^i.
"""

import argparse
from collections import Counter
from functools import cache
from math import gcd

from check_cubed_parity import X, polynomial
from check_factor_base import ratio_bound
from check_ore_norms import support
from make_witnesses import exact_quotient, mask_product, remainder


@cache
def odd_irreducibles(degree):
    return tuple(mask for mask in range((1 << degree) + 1, 1 << (degree + 1), 2)
                 if polynomial(support(mask)).is_irreducible())


def class_labels(cap):
    """Enumerate all monic constant-one g with polynomial Euler function at most cap."""
    primes = [(p, 1 << degree) for degree in range(1, (cap + 1).bit_length())
              for p in odd_irreducibles(degree)]

    def extend(start, degree, factors):
        yield degree, factors
        for index in range(start, len(primes)):
            prime, size = primes[index]
            new_degree = degree * (size - 1)
            if new_degree > cap:
                break
            power = 1
            while new_degree <= cap:
                yield from extend(index + 1, new_degree, factors + ((prime, power),))
                power += 1
                new_degree *= size

    yield from extend(0, 1, ())


@cache
def ore_power_table(seed):
    if seed < 3 or seed % 2 == 0:
        raise ValueError("the seed must have positive degree and constant term one")
    size = (1 << (seed.bit_length() - 1)) - 1
    powers = {}
    value = 1
    for index in range(size):
        if value in powers or not value:
            raise ValueError("the seed is not primitive")
        powers[value] = index
        value = remainder(value << 1, seed)
    if value != 1:
        raise ValueError("the seed is not primitive")
    return powers


def mobius_terms(factors):
    """Return all e dividing g for which mu(g/e) is nonzero, with its sign."""
    terms = [(1, 1)]
    for prime, multiplicity in factors:
        low = 1
        for _ in range(multiplicity - 1):
            low = mask_product(low, prime)
        high = mask_product(low, prime)
        terms = [(mask_product(e, multiplier), sign * coefficient)
                 for e, sign in terms for multiplier, coefficient in ((high, 1), (low, -1))]
    return terms


def single_orbit(factors):
    """Test whether Frobenius is transitive on the points of this exact additive order."""
    degrees = []
    for prime, multiplicity in factors:
        degree = prime.bit_length() - 1
        if multiplicity > 1 and (degree != 1 or multiplicity > 3):
            return False
        if any(gcd(degree, earlier) > 1 for earlier in degrees):
            return False
        try:
            ore_power_table(prime)
        except ValueError:
            return False
        degrees.append(degree)
    return True


@cache
def linearized_mask(label):
    return sum(1 << (1 << i) for i in support(label))


def class_identity(factors):
    numerator = denominator = 1
    terms = mobius_terms(factors)
    for e, sign in terms:
        if sign > 0:
            numerator = mask_product(numerator, linearized_mask(e))
        else:
            denominator = mask_product(denominator, linearized_mask(e))
    mask = exact_quotient(numerator, denominator)
    if mask_product(mask, denominator) != numerator:
        raise ArithmeticError("inexact class polynomial quotient")
    return mask, terms


def check_logs(seed, cap, show):
    logs = ore_power_table(seed)
    n = len(logs)
    if cap < 1:
        raise ValueError("choose a positive degree cap")
    modulus = polynomial((1 << i) - 1 for i in support(seed))
    if not modulus.is_irreducible():
        raise ArithmeticError("reducible Ore lift")
    size = (1 << n) - 1
    counts = Counter()
    singles = Counter()
    derivatives = 0
    for degree, factors in class_labels(cap):
        mask, terms = class_identity(factors)
        exponent = sum(sign * (1 << logs[residue]) for e, sign in terms
                       if (residue := remainder(e, seed)))
        factor = polynomial(support(mask))
        is_single = single_orbit(factors)
        if factor.degree() != degree or is_single != factor.is_irreducible():
            raise ArithmeticError(f"incorrect orbit classification for {factors}")
        value = factor % modulus
        vanishes = factors == ((seed, 1),)
        if vanishes:
            if value != 0:
                raise ArithmeticError("the exact seed class should vanish")
            value = factor.derivative() % modulus
            derivatives += 1
        if X.pow_mod(exponent % size, modulus) != value:
            raise ArithmeticError(f"incorrect logarithm for {mask:#x}")
        if vanishes:
            continue
        counts[degree] += 1
        if is_single:
            singles[degree] += 1
            if show:
                print(f"{degree} {mask:#x} {exponent % size:#x}")
    print(f"degree {n}, through factor degree {cap}: {sum(counts.values())} exact logarithms, "
          f"{sum(singles.values())} individual irreducibles")
    print("individual irreducibles by degree:", sorted(singles.items()))
    if derivatives:
        print("also verified the regularized logarithm of the vanishing seed class")


def lean_data():
    records = sorted(class_identity(factors) for _, factors in class_labels(31))
    labels = sorted({e for _, terms in records for e, _ in terms})
    first, second = (ore_power_table(seed) for seed in (0x805, 0xa01))
    print("private def seedLogs : List (ℕ × ℕ × ℕ) := [")
    print(",\n".join(f"  ({e:#x}, {first[e]}, {second[e]})" for e in labels) + "]")
    print("\ndef classes : List (ℕ × List ℕ × List ℕ) := [")
    result = []
    for mask, terms in records:
        sides = [", ".join(hex(e) for e, sign in terms if sign == s) for s in (1, -1)]
        result.append(f"  ({mask:#x}, [{sides[0]}], [{sides[1]}])")
    print(",\n".join(result) + "]")


def order_bound(s):
    n = (1 << s) - 1
    half = (n - 1) // 2
    weights = Counter(degree for degree, _ in class_labels(half))
    bound = ratio_bound(n, weights)
    print(f"seed degree {s}, lift degree {n}, {sum(weights.values())} class polynomials "
          f"of degree at most {half}")
    print(f"order >= {bound} > 2^{bound.bit_length() - 1}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=lambda arg: int(arg, 0),
                        help="primitive binary seed mask for checking logarithms")
    parser.add_argument("--cap", type=int, default=16, help="maximum class polynomial degree")
    parser.add_argument("--show", action="store_true", help="print individual masks and exponents in hex")
    parser.add_argument("--bound", type=int, help="calculate the uniform order bound in this seed degree")
    parser.add_argument("--lean-data", action="store_true", help="emit the degree-2047 Lean tables")
    args = parser.parse_args()
    if args.seed is None and args.bound is None and not args.lean_data:
        parser.error("supply --seed, --bound or --lean-data")
    if args.lean_data:
        lean_data()
    if args.bound is not None:
        if args.bound < 2:
            parser.error("use seed degree at least two")
        order_bound(args.bound)
    if args.seed is not None:
        check_logs(args.seed, args.cap, args.show)
