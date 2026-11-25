"""Check the parity sieve by binary polynomial factor degrees.

With no arguments, reproduce the 424 sample factorizations in the note.
Supply a degree and --cutoff to inspect one candidate in another degree,
or --sidon-count N to count every primitive Sidon-support pentanomial in
the given degree.
"""

import argparse
from itertools import combinations, combinations_with_replacement
from math import gcd as integer_gcd, lcm
from random import Random

from make_witnesses import gcd, prime_factors, square_mod, x_power


def residue_range(start, stop, residue, modulus):
    first = start + (residue - start) % modulus
    return range(first, stop, modulus)


def parameter_ranges(degree, period):
    """Return the lowest interior exponent and ranges of the next two."""
    n, L = degree, period
    if n <= 128 * L:
        raise ValueError(f"the counting bound requires degree > {128 * L}")
    if n % 2:
        h_mod_four = (3 * n + (0 if n % 8 in (3, 5) else 2)) % 4
        residue = L * (h_mod_four * pow(L, -1, 4) % 4)
        hs = residue_range(n // 4 + 1, (n + 2) // 3, residue, 4 * L)
        middle = range(2 * hs.start, 2 * hs.stop, 2 * hs.step)
        upper = residue_range(3 * n // 4 + 1, n, 8, 8 * L)
        return 8, middle, upper
    lowest = 4 if n % 8 == 4 else 2
    b_mod_four = n // 2 % 4 if n % 4 == 2 else 1
    residue = L * (b_mod_four * pow(L, -1, 4) % 4)
    middle = residue_range(n // 16 + 1, (n + 7) // 8, residue, 4 * L)
    upper = residue_range(n // 4 + 1, (n + 2) // 3, lowest, 2 * L)
    return lowest, middle, upper


def exact_quotient(f, g):
    quotient = 0
    while f.bit_length() >= g.bit_length():
        shift = f.bit_length() - g.bit_length()
        quotient ^= 1 << shift
        f ^= g << shift
    assert f == 0
    return quotient


def sidon(support):
    return len({a + b for a, b in combinations_with_replacement(support, 2)}) == 15


def count_primitive_sidon(n):
    """Use one candidate product, then remove all roots of proper order."""
    product = 1
    candidates = 0
    for middle in combinations(range(1, n), 3):
        support = (0, *middle, n)
        if sidon(support):
            next_product = 0
            for exponent in support:
                next_product ^= product << exponent
            product = next_product
            candidates += 1

    order = 2 ** n - 1
    remaining = gcd(product, x_power(order, product) ^ 1)
    for prime in sorted(set(prime_factors(order))):
        if remaining == 1:
            break
        lower_order = gcd(remaining, x_power(order // prime, remaining) ^ 1)
        remaining = exact_quotient(remaining, lower_order)
    degree = remaining.bit_length() - 1
    assert degree % n == 0
    return candidates, degree // n


def factor_degrees(f):
    """Distinct-degree factorization of a squarefree polynomial over F_2."""
    frobenius = 2
    degrees = []
    d = 1
    while f.bit_length() - 1 >= 2 * d:
        frobenius = square_mod(frobenius, f)
        block = gcd(f, frobenius ^ 2)
        if block != 1:
            block_degree = block.bit_length() - 1
            assert block_degree % d == 0
            degrees.extend([d] * (block_degree // d))
            f = exact_quotient(f, block)
        d += 1
    if f != 1:
        degrees.append(f.bit_length() - 1)
    return degrees


def check_degree(n, cutoff, random):
    period = lcm(*(2 ** d - 1 for d in range(1, cutoff + 1)))
    lowest, middle, upper = parameter_ranges(n, period)
    count = len(middle) * len(upper)
    assert 6144 * period ** 2 * count >= n ** 2
    support = (0, lowest, random.choice(middle), random.choice(upper), n)
    assert tuple(sorted(set(support))) == support and integer_gcd(*support) == 1
    assert sidon(support)
    f = sum(1 << i for i in support)
    derivative = sum(1 << (i - 1) for i in support if i % 2)
    assert gcd(f, derivative) == 1
    degrees = factor_degrees(f)
    assert sum(degrees) == n and min(degrees) > cutoff and len(degrees) % 2 == 1
    return support, degrees, count


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("degree", type=int, nargs="?")
    modes.add_argument("--sidon-count", type=int, metavar="N")
    parser.add_argument("--cutoff", type=int, default=1)
    args = parser.parse_args()
    random = Random(37633)
    if args.sidon_count is not None:
        if args.sidon_count < 1:
            parser.error("the degree must be positive")
        candidates, primitive = count_primitive_sidon(args.sidon_count)
        print(f"Degree {args.sidon_count}: {primitive} primitive among {candidates} Sidon supports.")
    elif args.degree is None:
        for cutoff, ns in ((1, range(129, 385)), (2, range(385, 545)), (3, range(2689, 2697))):
            for n in ns:
                check_degree(n, cutoff, random)
            print(f"Checked {len(ns)} degrees from {ns.start} through {ns.stop-1} at cutoff {cutoff}.")
    else:
        if args.cutoff < 1:
            parser.error("the cutoff must be positive")
        try:
            support, degrees, count = check_degree(args.degree, args.cutoff, random)
        except ValueError as error:
            parser.error(str(error))
        print(f"{count} candidates. Sample exponents {support}. Factor degrees {degrees}.")
