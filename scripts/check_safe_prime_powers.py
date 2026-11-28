"""Check the one-bit eleventh-power exceptions and safe-prime field-degree bounds."""

import argparse
from collections import Counter
from functools import reduce
from itertools import combinations
from math import gcd
from operator import xor

from check_cubed_parity import X, polynomial, reciprocal
from check_trinomial_subfield_pairs import prime_divisors


BASES = ((0, 1, 5, 9, 10), (0, 3, 5, 7, 10))


def bits(poly):
    return sum(int(c) << i for i, c in enumerate(poly.coeffs()))


def check_columns():
    # Work in F_2[T]/Phi_11. The element u generates its subfield F_4.
    phi = polynomial(range(11))
    u = polynomial((1, 3, 4, 5, 9))
    if not phi.is_irreducible() or (u**2 + u + 1) % phi != 0:
        raise ArithmeticError("incorrect model for the coefficient field F_4")
    columns = [tuple(bits(a * X**i % phi) for a in (X**0, u, u + 1)) for i in range(11)]
    for size, expected in ((4, {256: 330}), (5, {256: 55, 1024: 407})):
        spans = Counter()
        for support in combinations(columns, size):
            span = {0}
            for column in support:
                span |= {v ^ b for v in span for b in column}
            spans[len(span)] += 1
        if spans != expected:
            raise ArithmeticError(f"unexpected span sizes for {size} columns: {spans}")

    # Enumerate the sparse irreducible factors of X^33-1 themselves.
    factors = (X**33 + 1).factor()[1]
    found = set()
    for factor, multiplicity in factors:
        if multiplicity != 1 or not factor.is_irreducible():
            raise ArithmeticError("the order-33 factorization is not squarefree and irreducible")
        support = tuple(i for i, c in enumerate(factor.coeffs()) if c)
        if len(support) <= 5 and X.pow_mod(3, factor) != 1:
            found.add(support)
            if X.pow_mod(11, factor) == 1:
                raise ArithmeticError("a sparse order-11 factor survived")
    if found != set(BASES):
        raise ArithmeticError(f"unexpected normalized exceptions: {found}")
    print("All 330 four-column sets are independent over F_4. "
          "Exactly 55 of 462 five-column sets are dependent. Both sparse bases have order 33.")

    # Each factor selects one of the two Frobenius orbits of primitive 23rd roots.
    phi23 = polynomial(range(23))
    factors23 = phi23.factor()[1]
    if len(factors23) != 2 or any(f.degree() != 11 or k != 1 for f, k in factors23):
        raise ArithmeticError("unexpected factorization of Phi_23")
    for f, _ in factors23:
        columns = [bits(X**i % f) for i in range(23)]
        counts = [sum(reduce(xor, subset) == 0 for subset in combinations(columns, k))
                  for k in range(1, 8)]
        if counts != [0, 0, 0, 0, 0, 0, 253]:
            raise ArithmeticError(f"unexpected low weights at a primitive 23rd root: {counts}")
    print("Both length-23 binary codes have minimum weight seven, with 253 words of that weight.")


def power_degree(y, f, primes):
    degree = f.degree()
    for prime in primes:
        while degree % prime == 0:
            smaller = degree // prime
            if y.pow_mod((1 << smaller) - 1, f) != 1:
                break
            degree = smaller
    return degree


def is_exception(support, content):
    base = tuple(e // content for e in support)
    while content % 3 == 0:
        content //= 3
    return content == 1 and base in BASES


def check_degree_ten():
    survivors = set()
    irreducibles = 0
    for taps in combinations(range(1, 10), 3):
        support = (0, *taps, 10)
        f = polynomial(support)
        if f.is_irreducible():
            irreducibles += 1
            if all(X.pow_mod(1023 // p, f) != 1 for p in (3, 11)):
                survivors.add(support)
    excluded = {s for s in survivors if X.pow_mod(33, polynomial(s)) == 1}
    if (irreducibles, len(survivors)) != (38, 22) or excluded != set(BASES):
        raise ArithmeticError("the independent degree-ten prime-index census differs")
    print("Of 38 degree-ten irreducible pentanomials, 22 pass the tests for 3 and 11. "
          "Removing the two decoded exceptions leaves 20 primitive.")


def check_fields(limit):
    checked = exceptions = 0
    for n in range(2, limit + 1):
        primes = prime_divisors(n)
        for size in (1, 3):
            for taps in combinations(range(1, n), size):
                support = (0, *taps, n)
                if support > reciprocal(support):
                    continue
                f = polynomial(support)
                if not f.is_irreducible():
                    continue
                checked += 1
                content = gcd(*support)
                for ell in (11, 23, 47, 59):
                    index = n // power_degree(X**ell % f, f, primes)
                    if ell == 11:
                        exceptional = is_exception(support, content)
                        if (index % 5 == 0) != exceptional or (exceptional and index != 5):
                            raise ArithmeticError(f"unexpected eleventh-power index {index} at {support}")
                        exceptions += exceptional
                    elif index != gcd(ell, content) and not (ell == 59 and index == 2):
                        raise ArithmeticError(f"unexpected {ell}-power index {index} at {support}")
    print(f"Checked four powers of all {checked} sparse irreducible reciprocal classes "
          f"through degree {limit}, including {exceptions} eleventh-power exceptions.")


def check_dilations():
    for base in BASES:
        for i in range(6):
            g = 3**i
            f = polynomial(tuple(g * e for e in base))
            order = 33 * g
            if not f.is_irreducible() or X.pow_mod(order, f) != 1 or any(
                    X.pow_mod(order // p, f) == 1 for p in (3, 11)):
                raise ArithmeticError(f"incorrect dilation order in degree {10*g}")
    print("Verified the orders of both exceptional families through degree 2430.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", default=50, type=int)
    args = parser.parse_args()
    if args.through < 2:
        parser.error("use an upper degree of at least two")
    check_columns()
    check_degree_ten()
    check_dilations()
    check_fields(args.through)
