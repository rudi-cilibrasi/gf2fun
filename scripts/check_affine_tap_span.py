"""Find all divisibility-minimal moduli that exclude short three-tap shapes."""

import argparse
from functools import cache
from math import gcd, lcm, prod

from flint import fmpz, nmod_poly
from sympy import factorint


X = nmod_poly([0, 1], 2)


@cache
def field_order_primes(d):
    order = 2**d - 1
    factors = factorint(order)
    if prod(p**e for p, e in factors.items()) != order or not all(fmpz(p).is_prime() for p in factors):
        raise ArithmeticError(f"incomplete field order in degree {d}")
    return tuple(factors)


@cache
def root_order(coefficients):
    f = nmod_poly(list(coefficients), 2)
    order = 2**f.degree() - 1
    for p in field_order_primes(f.degree()):
        while order % p == 0 and X.pow_mod(order // p, f) == 1:
            order //= p
    return order


def minimal_divisors(values):
    """Keep exactly the minimal elements under divisibility."""
    kept = []
    for v in sorted(set(values)):
        if all(v % u for u in kept):
            kept.append(v)
    return tuple(kept)


@cache
def root_orders(d, j):
    factors = (1 + X**j + X**d).factor()[1]
    return minimal_divisors(root_order(tuple(map(int, f.coeffs()))) for f, _ in factors)


def complementary_shapes(d):
    # The shape on n-th roots is 1 + Y^(2c) + Y^(c+k), up to reversal.
    taps = set()
    for c in range(1, d//2 + 1):
        for k in range(1, d):
            if c != k and gcd(c, k) == 1 and c + max(c, k) == d:
                middle = min(2*c, c+k)
                taps.add(min(middle, d-middle))
    return taps


def blocking_moduli(clauses):
    mandatory = lcm(*(orders[0] for orders in clauses if len(orders) == 1))
    candidates = (mandatory,)
    for orders in sorted(clauses, key=lambda row: (len(row), row)):
        if all(mandatory % h for h in orders):
            candidates = minimal_divisors(lcm(n, h) for n in candidates for h in orders)
    return candidates


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=29, help="largest affine span")
    parser.add_argument("--complementary", action="store_true", help="use only normalized complementary shapes")
    args = parser.parse_args()
    if args.through < 2:
        parser.error("the span must be at least two")
    clauses = set()
    for d in range(2, args.through + 1):
        taps = complementary_shapes(d) if args.complementary else range(1, d//2 + 1)
        clauses.update(root_orders(d, j) for j in taps)
        moduli = blocking_moduli(clauses)
        print(d, *moduli)


if __name__ == "__main__":
    main()
