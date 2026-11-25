"""Count inverse pairs and product-one triples of roots of binary trinomials."""

import argparse
from math import gcd as integer_gcd

from check_exterior import fixed_dimension
from make_witnesses import gcd as polynomial_gcd, x_power


def pair_and_triple_counts(n, a):
    """Counts for X^n + X^a + 1 with relatively prime positive exponents."""
    if not 0 < a < n or integer_gcd(n, a) != 1:
        raise ValueError("the exponents must satisfy 0 < a < n and gcd(n,a) = 1")
    f = (1 << n) | (1 << a) | 1
    period = n * (n - a) + a * a
    exceptional = polynomial_gcd(f, x_power(period, f) ^ 1).bit_length() - 1
    pairs = int({n % 3, a % 3} == {1, 2})
    triples, leftover = divmod(exceptional - 2 * pairs, 3)
    if leftover or triples < 0:
        raise ArithmeticError("invalid decomposition into root orbits")
    return pairs, triples


def check_exterior_counts(limit):
    checked = 0
    for n in range(3, limit + 1):
        for a in range(1, n):
            if integer_gcd(n, a) != 1:
                continue
            actual = tuple(fixed_dimension(n, [0, a], k) for k in (2, 3))
            if actual != pair_and_triple_counts(n, a):
                raise ArithmeticError(f"exterior-power disagreement for n={n}, a={a}")
            checked += 1
    print(f"Checked both exterior-power dimensions for {checked} trinomials through degree {limit}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int, nargs="?", default=16)
    args = parser.parse_args()
    if args.limit < 3:
        parser.error("the degree limit must be at least three")
    check_exterior_counts(args.limit)
