"""Check the trinomial classification of split progression pentanomials and explicit full orders."""

import json
from itertools import combinations
from math import gcd, isqrt, prod
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
        if not irreducible(modulus(j, (tap,))):
            continue
        source = (0, tap, j)
        singletons = [s for s in source if sum(a % 3 == s % 3 for a in source) == 1]
        if len(singletons) != 1:
            raise ArithmeticError(f"incorrect residue pattern for {source}")
        e, f = (a-singletons[0] for a in source if a != singletons[0])
        support = lift_support(e, f, 2)
        if support in lifts:
            raise ArithmeticError(f"two source trinomials produced {support}")
        lifts.add(support)
    return lifts


def split_progressions(n):
    if n % 4 != 2:
        return set()
    j = n//2
    lifts = quadratic_lifts(j)
    d = 1
    while j % 3 == 0:
        j //= 3
        d *= 3
    if d > 1:
        lifts.update(tuple(d*e for e in support) for support in quadratic_lifts(j))
    return lifts


def direct_splits(n):
    x = polynomial(2)
    groups = [((1 << i)-1)*((1 << (n//i))-1) for i in range(2, isqrt(n)+1)
              if n % i == 0 and gcd(i, n//i) == 1]
    splits = set()
    if not groups:
        return splits
    for taps in combinations(range(1, n), 3):
        support = (0, *taps, n)
        if not any(2*b == a+c for a, b, c in combinations(support, 3)):
            continue
        f = modulus(n, taps)
        if any(x.pow_mod(group, f) == 1 for group in groups) and irreducible(f):
            splits.add(support)
    return splits


def main():
    total = normalized = dilated = 0
    for n in range(5, 97):
        generated = split_progressions(n)
        direct = direct_splits(n)
        if generated != direct:
            raise ArithmeticError(f"split support sets disagree in degree {n}: {generated ^ direct}")
        total += len(direct)
        normalized += sum(gcd(*s) == 1 for s in direct)
        dilated += sum(all(e % 3 == 0 for e in s) for s in direct)
    print(f"Degrees 5 through 96: {total} split progression supports, {normalized} with exponent gcd one, "
          f"{dilated} with every exponent divisible by three.")
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
