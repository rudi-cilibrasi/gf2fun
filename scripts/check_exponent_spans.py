"""Test necessary root-order bounds from the support of an irreducible binary polynomial."""

import argparse
from functools import cache
from itertools import combinations
from math import gcd

from sympy import n_order


@cache
def frobenius_period(k):
    return 1 if k == 1 else int(n_order(2, k))


def circular_span(support, multiplier, period):
    residues = sorted({(multiplier * e) % period for e in support})
    gaps = [b - a for a, b in zip(residues, residues[1:])]
    gaps.append(period + residues[0] - residues[-1])
    return period - max(gaps)


def pentanomial_shape_obstruction(support, period):
    """Apply the lattice volume bounds for triples, parallelograms and two progressions."""
    n = support[-1]
    for a, b, c in combinations(support, 3):
        width = (c - a) // gcd(b - a, c - a)
        if 2 * width * period**2 < n**3:
            return f"three exponents in a progression of width {width}"
    for a, b, c, d in combinations(support, 4):
        if a + d == b + c and 3 * period**2 < n**3:
            return f"the parallelogram {a}, {b}, {c}, {d}"
    # Each partition of five positions has a unique smaller row of length one or two.
    for size in (1, 2):
        for first in combinations(support, size):
            second = [e for e in support if e not in first]
            gaps = [e - row[0] for row in (first, second) for e in row]
            step = gcd(*gaps)
            small, large = sorted((row[-1] - row[0]) // step for row in (first, second))
            if 4 * large**2 * period < (3 * large - small) * n**2:
                return f"two progressions of widths {small} and {large} with step {step}"
    return None


def span_obstruction(support, period):
    """Return one multiplier proving the root order cannot divide this odd period."""
    n = support[-1]
    if period < n:
        return f"period {period} is below degree {n}"
    if len(support) == 5:
        shape = pentanomial_shape_obstruction(support, period)
        if shape:
            return shape
    for u in range(1, period // 2 + 1):
        k = gcd(u, period)
        orbit = frobenius_period(k)
        width = circular_span(support, u, period)
        if orbit * width < n * k:
            return f"multiplier {u}, gcd {k}, coset orbit bound {orbit}, circular span {width}"
    return None


def check_small(limit, sweep):
    from check_factor_base import irreducible, polynomial
    from check_ore_lifts import order_index
    from make_witnesses import mersenne_factors

    count = swept = 0
    for n in range(4, limit + 1):
        factors = mersenne_factors(n)
        for taps in combinations(range(1, n), 3):
            if gcd(n, *taps) != 1:
                continue
            support = (0, *taps, n)
            if not irreducible(polynomial(sum(1 << i for i in support))):
                continue
            h = ((1 << n) - 1) // order_index(support, factors)
            lower = 5 * n**4 + (10 * n**2 + 1 if n % 2 else 0)
            if 16 * h**3 < lower:
                raise ArithmeticError(f"packing bound failed at {support}, order {h}")
            count += 1
            if pentanomial_shape_obstruction(support, h):
                raise ArithmeticError(f"shape bound failed at {support} with order {h}")
            if h <= sweep:
                witness = span_obstruction(support, h)
                if witness is not None:
                    raise ArithmeticError(f"span bound failed at {support}, order {h}, {witness}")
                swept += 1
    print(f"Checked the packing bound for {count} irreducible pentanomials with exponent gcd one "
          f"through degree {limit}. Tested every multiplier up to sign for {swept} orders at most {sweep}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=20)
    parser.add_argument("--sweep", type=int, default=1000)
    parser.add_argument("--support", nargs="+", type=int)
    parser.add_argument("--period", type=int)
    args = parser.parse_args()
    if args.support is not None or args.period is not None:
        if not args.support or args.period is None or args.period < 1 or args.period % 2 == 0:
            parser.error("provide a support and a positive odd period")
        support = sorted(set(args.support))
        if len(support) != len(args.support) or len(support) < 2 or support[0] != 0 or gcd(*support) != 1:
            parser.error("the support must be distinct, nonnegative, contain zero, and have gcd one")
        witness = span_obstruction(support, args.period)
        print(f"Excluded by {witness}." if witness else "All multiplier inequalities hold.")
    else:
        if args.through < 4 or args.sweep < 1:
            parser.error("use a degree limit of at least four and a positive sweep limit")
        check_small(args.through, args.sweep)
