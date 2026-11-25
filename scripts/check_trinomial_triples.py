"""Count inverse pairs and product-one triples of roots of binary trinomials."""

import argparse
from math import gcd as integer_gcd

from check_exterior import fixed_dimension
from make_witnesses import gcd as polynomial_gcd, remainder, square_mod, x_power


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


def has_irreducible_root_triple(mask):
    """Can two conjugates of X multiply to the inverse of a third?"""
    degree = mask.bit_length() - 1
    # Frobenius transitivity lets us fix the first conjugate at X.
    root = 2
    inverse = mask >> 1
    products, inverses = set(), set()
    for _ in range(degree):
        products.add(remainder(root << 1, mask))
        inverses.add(inverse)
        root = square_mod(root, mask)
        inverse = square_mod(inverse, mask)
    return not products.isdisjoint(inverses)


def exceptional_trinomials(limit):
    cases = set()
    for base, prime in ((2, 3), (3, 7), (9, 73)):
        degree, tap = base, 1
        while degree <= limit:
            cases.update(((degree, tap), (degree, degree - tap)))
            degree *= prime
            tap *= prime
    return cases


def check_irreducible_trinomials(limit):
    from check_factor_base import irreducible, polynomial

    found = set()
    checked = 0
    for n in range(2, limit + 1):
        for a in range(1, n):
            mask = (1 << n) | (1 << a) | 1
            if irreducible(polynomial(mask)):
                checked += 1
                if has_irreducible_root_triple(mask):
                    found.add((n, a))
    expected = exceptional_trinomials(limit)
    if found != expected:
        raise ArithmeticError(f"missing {sorted(expected-found)}, unexpected {sorted(found-expected)}")
    print(f"Checked all {checked} irreducible trinomials through degree {limit}. "
          f"Found {len(found)} with a product-one triple in degrees {sorted({n for n, _ in found})}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int, nargs="?", default=16)
    parser.add_argument("--irreducibles", action="store_true",
                        help="check the classification using FLINT and direct Frobenius orbits")
    args = parser.parse_args()
    if args.limit < 3:
        parser.error("the degree limit must be at least three")
    if args.irreducibles:
        check_irreducible_trinomials(args.limit)
    else:
        check_exterior_counts(args.limit)
