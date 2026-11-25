"""Test the first four exterior powers using the minimal polynomial of root pairs."""

import argparse

from check_exterior import fixed_dimension
from make_witnesses import exact_quotient, gcd, mask_product, remainder


def derivative(f):
    odd_powers = sum(1 << i for i in range(1, f.bit_length(), 2))
    return (f & odd_powers) >> 1


def reciprocal(f):
    return int(f"{f:b}"[::-1], 2)


def polynomial_lcm(a, b):
    return mask_product(exact_quotient(a, gcd(a, b)), b)


def scalar_annihilator(powers, i, j):
    """Berlekamp–Massey on coordinate i,j of X^k ∧ X^(k+1) modulo f."""
    recurrence = previous = 1
    length = 0
    gap = 1
    window = 0
    for k in range(len(powers) - 1):
        a, b = powers[k:k + 2]
        bit = (((a >> i) & (b >> j)) ^ ((a >> j) & (b >> i))) & 1
        window = (window << 1) | bit
        if (recurrence & window).bit_count() % 2:
            updated = recurrence ^ (previous << gap)
            if 2 * length <= k:
                length, previous, gap = k + 1 - length, recurrence, 0
            recurrence = updated
        gap += 1
    return int(f"{recurrence:0{length + 1}b}"[::-1], 2)


def surviving_coordinate(annihilator, powers, degree):
    """Evaluate the proposed relation on the entire bivector, exactly."""
    rows = [0] * degree
    terms = annihilator
    while terms:
        lowest = terms & -terms
        k = lowest.bit_length() - 1
        a, b = powers[k:k + 2]
        for left, right in ((a, b), (b, a)):
            while left:
                bit = left & -left
                rows[bit.bit_length() - 1] ^= right
                left ^= bit
        terms ^= lowest
    for i, row in enumerate(rows):
        if row:
            return i, (row & -row).bit_length() - 1
    return None


def pair_polynomial(f):
    """Return the squarefree polynomial on all products of two distinct roots."""
    degree = f.bit_length() - 1
    if degree <= 0 or not f & 1:
        raise ValueError("a monic polynomial of positive degree and constant term 1 is required")
    if gcd(f, derivative(f)) != 1:
        raise ValueError("the polynomial must be squarefree")

    dimension = degree * (degree - 1) // 2
    if dimension == 0:
        return 1
    powers = [1]
    for _ in range(2 * dimension):
        powers.append(remainder(powers[-1] << 1, f))

    annihilator = 1
    while coordinate := surviving_coordinate(annihilator, powers, degree):
        scalar = scalar_annihilator(powers, *coordinate)
        updated = polynomial_lcm(annihilator, scalar)
        if updated == annihilator or updated.bit_length() > dimension + 1:
            raise ArithmeticError("a surviving coordinate must increase the minimal polynomial")
        annihilator = updated
    return annihilator


def reciprocal_defects(f):
    """Degrees of the reciprocal gcds detecting products of lengths ≤2, ≤3, ≤4."""
    pairs = polynomial_lcm(f, pair_polynomial(f))
    reverse = reciprocal(pairs)
    return tuple(g.bit_length() - 1 for g in
                 (gcd(f, reciprocal(f)), gcd(f, reverse), gcd(pairs, reverse)))


def compare_exterior(limit):
    checked = 0
    for degree in range(1, limit + 1):
        for f in range((1 << degree) | 1, 1 << (degree + 1), 2):
            if gcd(f, derivative(f)) != 1:
                continue
            taps = [i for i in range(degree) if f >> i & 1]
            nullities = [fixed_dimension(degree, taps, k) for k in range(1, min(degree, 4) + 1)]
            predicted = reciprocal_defects(f)
            if any((d == 0) != (not any(nullities[:k])) for k, d in zip((2, 3, 4), predicted)):
                raise ArithmeticError(f"exterior-power disagreement at degree {degree}, mask {f:#x}")
            checked += 1
    print(f"Checked all {checked} squarefree constant-one polynomials through degree {limit}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare", type=int, help="cross-check all squarefree polynomials through this degree")
    parser.add_argument("degree", type=int, nargs="*", help="n for X^n + X^5 + X^3 + X^2 + 1")
    args = parser.parse_args()
    if args.compare is not None:
        if args.compare < 1:
            parser.error("comparison degree must be positive")
        compare_exterior(args.compare)
    for n in args.degree or ([] if args.compare is not None else [8, 16, 32, 64, 128]):
        if n <= 5:
            parser.error("the five-term family requires n > 5")
        f = (1 << n) | 0x2d
        print(f"n={n}, gcd degrees through lengths 2, 3, 4 = {reciprocal_defects(f)}, "
              f"gcd with X^32-X = {gcd(f, (1 << 32) ^ 2):#x}", flush=True)
