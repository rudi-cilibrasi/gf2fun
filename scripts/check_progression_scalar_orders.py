"""Check root orders for pentanomials containing three consecutive exponents."""

import json
from itertools import combinations
from math import gcd, prod
from pathlib import Path

from flint import fmpz

from check_degree_1229 import check_trinomials
from check_dyadic_scalar_lifts import lift_support
from check_factor_base import irreducible, modulus, polynomial
from check_product_range import prime_index_powers


DATA = Path(__file__).resolve().parents[1] / "data"


def check_order(n, tap, order, primes):
    f = modulus(n, (1, 2, tap))
    x = polynomial(2)
    if prod(primes) != order or not all(fmpz(p).is_prime() for p in set(primes)):
        raise ArithmeticError(f"incomplete order factorization in degree {n}")
    if not irreducible(f) or x.pow_mod(order, f) != 1:
        raise ArithmeticError(f"degree or order test failed in degree {n}")
    if any(value == 1 for _, value in prime_index_powers(x, order, sorted(set(primes)), f)):
        raise ArithmeticError(f"a proper divisor is an order in degree {n}")


def quadratic_lifts(j):
    lifts = set()
    for tap in range(1, j):
        if gcd(tap, j) != 1 or not irreducible(modulus(j, (tap,))):
            continue
        source = (0, tap, j)
        for singleton in source:
            e, f = (a-singleton for a in source if a != singleton)
            if e % 3 and (e-f) % 3 == 0:
                lifts.add(lift_support(e, f, 2))
    return lifts


def direct_splits(j):
    n = 2*j
    x = polynomial(2)
    group = 3*((1 << j)-1)
    splits = set()
    for taps in combinations(range(1, n), 3):
        if gcd(n, *taps) != 1:
            continue
        support = (0, *taps, n)
        if not any(2*b == a+c for a, b, c in combinations(support, 3)):
            continue
        f = modulus(n, taps)
        if x.pow_mod(group, f) == 1 and irreducible(f):
            splits.add(support)
    return splits


def main():
    total = 0
    for j in range(3, 36, 2):
        generated = quadratic_lifts(j)
        if generated != direct_splits(j):
            raise ArithmeticError(f"split support sets disagree in degree {2*j}")
        total += len(generated)
    print(f"Verified {total} normalized split supports containing a progression in degrees 6 through 70.")
    check_trinomials()
    print("Degree 2458 has no split pentanomial containing a three-term progression.")
    check_order(6, 4, 21, [3, 7])
    print("Degree 6 has a split root of exact order 21 with taps 1, 2 and 4.")
    for n, tap, table in ((1233, 43, "mersenne-1230-1280-factors.json"),
                          (3375, 491, "mersenne-3201-3456.json")):
        factors = json.loads((DATA / table).read_text())[str(n)]
        check_order(n, tap, (1 << n) - 1, factors)
        print(f"Degree {n} is primitive with taps 1, 2 and {tap}.")


if __name__ == "__main__":
    main()
