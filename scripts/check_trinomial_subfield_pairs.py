"""Compare the degree-only trinomial subfield test with direct finite-field powers."""

import argparse
from functools import cache
from itertools import combinations
from math import gcd, lcm

from flint import fmpz

from check_factor_base import irreducible, modulus, polynomial


@cache
def prime_divisors(n):
    return tuple(int(p) for p, _ in fmpz(n).factor())


@cache
def required_degrees(n, g):
    if g % 2 == 0:
        raise ValueError("an irreducible binary trinomial has odd exponent gcd")
    degrees = [n // g]
    for ell in prime_divisors(g):
        power = 1
        while n % (power * ell) == 0:
            power *= ell
        order = 1
        while pow(2, order, ell) != 1:
            order += 1
        degrees.append(power * order)
    return degrees


def verify(limit):
    x = polynomial(2)
    irreducibles = tests = splits = 0
    for n in range(2, limit + 1):
        proper = [d for d in range(1, n) if n % d == 0]
        pairs = [(d, e, lcm((1 << d) - 1, (1 << e) - 1))
                 for d, e in combinations(proper, 2) if lcm(d, e) == n]
        for k in range(1, n // 2 + 1):
            f = modulus(n, (k,))
            if not irreducible(f):
                continue
            irreducibles += 1
            g = gcd(k, n)
            degrees = required_degrees(n, g)
            for d, e, exponent in pairs:
                predicted = all(d % t == 0 or e % t == 0 for t in degrees)
                actual = x.pow_mod(exponent, f) == 1
                if predicted != actual:
                    raise ArithmeticError((n, k, d, e, predicted, actual))
                p, q = n // d, n // e
                if p in prime_divisors(n) and q in prime_divisors(n):
                    maximal = gcd(g, p*q, (1 << (n // (p*q))) - 1) > 1
                    if maximal != actual:
                        raise ArithmeticError((n, k, p, q, maximal, actual))
                tests += 1
                splits += actual
    print(f"Through {limit}: {irreducibles} irreducible trinomials up to reciprocal, "
          f"{tests} spanning subfield pairs tested, {splits} split roots.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=384)
    verify(parser.parse_args().through)
