"""Check which prime-power divisors of the lifted degree must occur together in an order.

The binary polynomial comparison uses only the seed and the selected prime
divisors of the lifted degree. --direct also powers X in the lifted quotient.
"""

import argparse
from itertools import combinations
from math import prod

from flint import nmod_poly
from sympy import factorint

from check_ore_lifts import lifted_support
from check_ore_norms import from_support, support
from make_witnesses import mask_product, primitive, remainder, x_power


def common_scale(inputs, seed, s, d):
    """Find a nonzero binary combination of columns killing all top d coordinates."""
    pivots = {}
    for j in range(s):
        column = 0
        for a in inputs:
            high = remainder(a << j, seed) >> (s-d)
            column = (column << d) | high
        scalar = 1 << j
        while column:
            i = column.bit_length() - 1
            if i not in pivots:
                pivots[i] = column, scalar
                break
            vector, combination = pivots[i]
            column ^= vector
            scalar ^= combination
        if column == 0:
            return scalar
    raise ValueError("the coordinate conditions have no nonzero solution")


def check_component(seed, primes, direct):
    s = seed.bit_length() - 1
    n = 2**s - 1
    k = len(primes)
    d = max(0, k-2)
    # Each move toggles one direction in the product of the (2^(n/p)-1).
    terms = [(0, 0)]
    for p in primes:
        terms += [(j+n//p, parity ^ 1) for j, parity in terms]
    inputs = [x_power(j % n, seed) for j, _ in terms]
    if len(set(inputs)) != 2**k:
        raise ValueError("the conjugate indices coincide")
    scalar = common_scale(inputs, seed, s, d)
    products = [1, 1]
    for a, (_, parity) in zip(inputs, terms, strict=True):
        g = remainder(mask_product(a, scalar), seed)
        if not 0 < g < 2**(s-d):
            raise ValueError("incorrect scale")
        quotient = sum(1 << (2**i-1) for i in support(g))
        products[parity] = mask_product(products[parity], quotient)
    if max(products).bit_length() > n or products[0] == products[1]:
        raise ValueError("comparison did not separate the two products below the field degree")
    if direct:
        modulus = from_support(lifted_support(support(seed)))
        exponent = prod(2**(n//p)-1 for p in primes)
        x = nmod_poly([0, 1], 2)
        if x.pow_mod(exponent, modulus) == 1:
            raise ValueError("direct quotient powering failed")
    return scalar


def all_sparse_seeds(s):
    factors = factorint(2**s-1)
    for size in (1, 3):
        for taps in combinations(range(1, s), size):
            seed = (1 << s) + 1 + sum(1 << j for j in taps)
            if primitive(s, seed, factors):
                yield seed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, required=True, help="seed degree")
    parser.add_argument("--directions", type=int, nargs="+", help="distinct primes dividing 2^s-1")
    parser.add_argument("--taps", type=int, nargs="+", help="interior exponents of a single primitive seed")
    parser.add_argument("--direct", action="store_true", help="also compute the power in the lifted field with FLINT")
    args = parser.parse_args()
    s = args.degree
    if s < 2:
        parser.error("seed degree must be at least 2")
    n = 2**s-1
    factors = factorint(n)
    primes = args.directions or sorted(factors)
    if len(set(primes)) != len(primes) or any(p not in factors for p in primes):
        parser.error("each direction must be a distinct prime divisor of the lifted degree")
    if args.taps:
        if len(set(args.taps)) != len(args.taps) or not all(0 < j < s for j in args.taps):
            parser.error("interior exponents must be distinct and strictly between 0 and the degree")
        seed = (1 << s) + 1 + sum(1 << j for j in args.taps)
        if not primitive(s, seed, factors):
            parser.error("the supplied seed is not primitive")
        seeds = [seed]
    else:
        seeds = all_sparse_seeds(s)
    count = 0
    for seed in seeds:
        check_component(seed, primes, args.direct)
        count += 1
    if count == 0:
        raise ValueError("no primitive seeds checked")
    method = " and direct FLINT powers" if args.direct else ""
    print(f"Lifted degree {n}, directions {primes}: verified {count} seeds "
          f"by polynomial comparison{method}.")


if __name__ == "__main__":
    main()
