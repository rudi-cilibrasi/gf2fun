"""Classify irreducible pentanomials whose third or fifth power lands in the half field."""

import argparse
from collections import Counter
from functools import cache
from itertools import combinations, product
from math import gcd

from flint import fmpz

from check_cubed_supports import restrict
from check_factor_base import irreducible, modulus, polynomial
from power_images import direction, norm_pattern, power_characteristic, residue_profiles


# Primitive exponent supports up to reciprocation, with the exact order of X.
EXCEPTIONS = {
    3: {(0, 1, 3, 8, 10): 93},
    5: {(0, 1, 2, 3, 4): 5, (0, 1, 2, 4, 12): 315,
        (0, 2, 6, 9, 12): 315, (0, 3, 15, 24, 28): 81915},
}


def canonical(exponents):
    exponents = sorted(exponents)
    left = tuple(x-exponents[0] for x in exponents)
    return min(left, tuple(left[-1]-x for x in reversed(left)))


def in_family(points, residues, ell):
    """Try each possible origin of the translate of {0,u,v,(ell-1)u,(ell-1)v}."""
    support = set(points)
    for i, origin in enumerate(points):
        for j, k in combinations(range(5), 2):
            if residues[j] == residues[i] or residues[j] != residues[k]:
                continue
            doubled = [tuple(a+(ell-1)*(b-a) for a, b in zip(origin, points[t]))
                       for t in (j, k)]
            if {origin, points[j], points[k], *doubled} == support:
                return True
    return False


def in_integer_family(support, ell):
    return in_family([(e,) for e in support], [e % ell for e in support], ell)


def classify(ell):
    # In an irreducible cubic twist the three residue classes have sizes 2,2,1.
    profiles = [(0, 0, 1, 1, 2)] if ell == 3 else residue_profiles(ell)
    initial = ((0, 0, 0, 0), *(tuple(int(i == j) for j in range(4)) for i in range(4)))
    rays = set()
    for residues in profiles:
        pattern = norm_pattern(ell, residues)
        for tail in product(range(2), repeat=4):
            if not any(tail):
                continue
            parities = (0, *tail)
            for target in range(2):
                # Translating the origin may switch the common parity of the norm.
                forbidden = [mix for mix in pattern if sum(c*b for c, b in zip(mix, parities)) % 2 != target]
                if len(forbidden) % 2:
                    continue

                @cache
                def visit(points):
                    if len(set(points)) < 5:
                        return
                    if len(points[0]) == 1:
                        rays.add(canonical(x for x, in points))
                        return
                    columns = tuple(zip(*points))
                    counts = Counter(tuple(sum(a*b for a, b in zip(mix, col)) for col in columns)
                                     for mix in forbidden)
                    odd = sorted(v for v, c in counts.items() if c % 2)
                    if not odd:
                        if not in_family(points, residues, ell):
                            raise ArithmeticError(f"unclassified family for {residues}: {points}")
                        return
                    # The first odd monomial must coincide with another odd one.
                    equations = {direction(tuple(a-b for a, b in zip(odd[0], other)))
                                 for other in odd[1:]}
                    for equation in equations:
                        visit(restrict(points, equation))

                visit(initial)
                visit.cache_clear()

    exceptions = {}
    x = polynomial(2)
    for support in sorted(rays):
        n = support[-1]
        if n % 2 or in_integer_family(support, ell):
            continue
        f = modulus(n, support[1:-1])
        if not irreducible(f) or not all(e % 2 == 0 for e in power_characteristic(support, ell)):
            continue
        order = (1 << n)-1
        for prime, multiplicity in fmpz(order).factor():
            prime = int(prime)
            for _ in range(multiplicity):
                if x.pow_mod(order//prime, f) != 1:
                    break
                order //= prime
        exceptions[support] = order
    if exceptions != EXCEPTIONS[ell]:
        raise ArithmeticError(f"unexpected isolated supports for {ell}: {exceptions}")
    print(f"Power {ell}: one parametric shape and {len(exceptions)} isolated irreducible supports up to reciprocity.")


def crosscheck(limit):
    """Independently test the half-field criterion on every undilated irreducible through limit."""
    x = polynomial(2)
    checked = 0
    for n in range(4, limit+1, 2):
        q = 1 << (n//2)
        for taps in combinations(range(1, n), 3):
            s = (0, *taps, n)
            if gcd(*s) != 1 or s != canonical(s):
                continue
            f = modulus(n, taps)
            if not irreducible(f):
                continue
            for ell in EXCEPTIONS:
                expected = s in EXCEPTIONS[ell] or in_integer_family(s, ell)
                if (x.pow_mod(ell*(q-1), f) == 1) != expected:
                    raise ArithmeticError(f"half-field test disagrees at {s}, power {ell}")
            checked += 1
    print(f"Direct field powering agrees on {checked} irreducible reciprocal classes through degree {limit}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=36)
    args = parser.parse_args()
    for ell in EXCEPTIONS:
        classify(ell)
    crosscheck(args.through)
