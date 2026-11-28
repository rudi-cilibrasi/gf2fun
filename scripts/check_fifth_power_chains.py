"""Classify normalized pentanomials with a sparse fifth-power norm in every degree.

Run with uv run --no-project --with python-flint==0.9.0 python scripts/check_fifth_power_chains.py.
"""

import argparse
from collections import Counter
from itertools import combinations
from math import gcd

from check_cubed_parity import X, polynomial
from check_cubing_chains import primitive
from power_images import classify_profile, norm_pattern, power_characteristic, residue_profiles


def audit():
    exceptions = set()
    profiles = []
    for residues in residue_profiles(5):
        if len(norm_pattern(5, residues)) % 2 == 0:
            continue
        sources = classify_profile(5, residues)
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
            if len(power_characteristic(support, 5)) <= 5:
                direct.add(support)
    if direct != {s for s in exceptions if s[-1] <= 25}:
        raise ArithmeticError("the independent low-degree enumeration disagrees")
    irreducibles = set()
    primitive_images = {}
    primitive_targets = 0
    for s in exceptions:
        image = power_characteristic(s, 5)
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
    chains = Counter()
    for n in range(5, 26):
        sources = {s for s in primitive_images if s[-1] == n}
        sources.update((0, a, n) for a in range(1, n) if primitive(polynomial((0, a, n)), n))
        for s in sources:
            if len(power_characteristic(s, 5)) <= 5 and len(power_characteristic(s, 25)) <= 5:
                chains[n] += 1
    if chains != {5: 6, 6: 6, 7: 6, 9: 2, 10: 6, 11: 2, 13: 2}:
        raise ArithmeticError("unexpected sparse fifth-power chains")
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
