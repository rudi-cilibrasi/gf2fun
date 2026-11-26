"""Classify normalized pentanomials with a sparse fifth-power norm in every degree.

Run with uv run --no-project --with python-flint==0.9.0 python scripts/check_fifth_power_chains.py.
"""

import argparse
from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement
from math import gcd

from flint import nmod_mat

from check_cubed_parity import X, polynomial, reciprocal
from check_cubed_supports import restrict
from check_cubing_chains import primitive
from power_images import norm_pattern


def residue_profiles():
    """Five labels modulo translation, invertible scaling and permutation."""
    return sorted({min(tuple(sorted(a*(r-b) % 5 for r in residues))
                       for a in range(1, 5) for b in residues)
                   for residues in combinations_with_replacement(range(5), 5)
                   if 1 < len(set(residues)) < 5})


def direction(vector):
    divisor = gcd(*vector)
    if next(x for x in vector if x) < 0:
        divisor = -divisor
    return tuple(x//divisor for x in vector)


def classify_profile(residues):
    pattern = norm_pattern(5, residues)
    exceptions = set()

    @cache
    def visit(points):
        if len(set(points)) < 5:
            return
        columns = tuple(zip(*points))
        terms = Counter(tuple(sum(i*x for i, x in zip(mix, col)) for col in columns)
                        for mix in pattern)
        odd = sorted(t for t, multiplicity in terms.items() if multiplicity % 2)
        if len(odd) <= 5:
            raise ArithmeticError(f"positive-dimensional sparse family for {residues}: {points}")
        if len(columns) > 2:
            # At least one of any six survivors must collide with another survivor.
            equations = {direction(tuple(a-b for a, b in zip(t, u)))
                         for i, t in enumerate(odd[:6]) for u in odd[i+1:]}
            for equation in equations:
                visit(restrict(points, equation))
            return

        # On a line every collision has the same normal direction. A colliding
        # pair removes at most two terms, including when several pairs coincide.
        pairs = Counter(direction((a-c, b-d)) for (a, b), (c, d) in combinations(odd, 2))
        for (u, v), count in pairs.items():
            if 2*count < len(odd)-5:
                continue
            values = [v*a-u*b for a, b in points]
            if len(set(values)) != 5:
                continue
            scale = gcd(*values)
            exponents = [x//scale for x in values]
            if not any(all((k*x-r) % 5 == 0 for x, r in zip(exponents, residues)) for k in range(1, 5)):
                continue
            image = Counter(v*a-u*b for a, b in odd)
            if sum(c % 2 for c in image.values()) <= 5:
                support = tuple(x-min(exponents) for x in sorted(exponents))
                exceptions.update((support, reciprocal(support)))

    visit(((0, 0, 0, 0), *(tuple(int(i == j) for j in range(4)) for i in range(4))))
    visit.cache_clear()
    return exceptions


def fifth_characteristic(support):
    """Characteristic polynomial of multiplication by X^5 modulo F, including reducible F."""
    n = support[-1]
    modulus = sum(1 << e for e in support)
    column = 1
    transpose = []
    for i in range(n+5):
        if i >= 5:
            transpose.extend((column >> j) & 1 for j in range(n))
        column <<= 1
        if column >> n:
            column ^= modulus
    coefficients = nmod_mat(n, n, transpose, 2).charpoly()
    return tuple(i for i in range(n+1) if coefficients[i])


def audit():
    exceptions = set()
    profiles = []
    for residues in residue_profiles():
        sources = classify_profile(residues)
        if sources & exceptions:
            raise ArithmeticError("overlapping residue profiles")
        exceptions.update(sources)
        profiles.append((residues, len(norm_pattern(5, residues)), len(sources),
                         max((s[-1] for s in sources), default=0)))
    if len(exceptions) != 322 or {s for s in exceptions if s[-1] >= 85} != {
            (0, 1, 5, 21, 85), (0, 64, 80, 84, 85)}:
        raise ArithmeticError("unexpected normalized exceptional supports")

    # All supports through the largest primitive exception, without using
    # residue profiles or collision equations, and every exception above it.
    direct = set()
    for taps in combinations(range(1, 26), 4):
        support = (0, *taps)
        if gcd(*taps) == 1 and len({e % 5 for e in support}) < 5:
            if len(fifth_characteristic(support)) <= 5:
                direct.add(support)
    if direct != {s for s in exceptions if s[-1] <= 25}:
        raise ArithmeticError("the independent low-degree enumeration disagrees")
    irreducibles = set()
    primitive_images = {}
    primitive_targets = 0
    for s in exceptions:
        image = fifth_characteristic(s)
        f, g = polynomial(s), polynomial(image)
        if len(image) > 5 or g.compose_mod(X**5, f) != 0:
            raise ArithmeticError(f"direct characteristic polynomial failed at {s}")
        if f.is_irreducible():
            irreducibles.add(s)
            if primitive(f, s[-1]):
                if not g.is_irreducible() or g.degree() != f.degree():
                    raise ArithmeticError("the powered primitive root lost degree")
                primitive_images[s] = image
                primitive_targets += primitive(g, s[-1])
    expected = {5: 4, 6: 4, 7: 6, 8: 4, 9: 6, 10: 8, 11: 8, 12: 6, 13: 8,
                15: 4, 16: 4, 17: 4, 18: 2, 19: 2, 25: 2}
    if len(irreducibles) != 102 or max(s[-1] for s in irreducibles) != 25:
        raise ArithmeticError("unexpected irreducible sources")
    if Counter(s[-1] for s in primitive_images) != expected or primitive_targets != 58:
        raise ArithmeticError("unexpected primitive sources or targets")
    if primitive_images.get((0, 8, 9, 13, 25)) != (0, 15, 17, 20, 25):
        raise ArithmeticError("the degree-25 pair changed")
    return profiles, primitive_images


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="print every primitive source and its fifth-power image")
    args = parser.parse_args()
    profiles, images = audit()
    print("Residues, formal terms, normalized exceptions, largest degree")
    for residues, terms, count, largest in profiles:
        print("".join(map(str, residues)), terms, count, largest or "–")
    print("322 normalized supports; 102 irreducible and 72 primitive. Largest primitive degree: 25.")
    print("58 of the primitive sources have primitive fifth-power images.")
    if args.list:
        for source in sorted(images, key=lambda s: (s[-1], s)):
            print(*source, "->", *images[source])
