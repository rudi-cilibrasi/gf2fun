"""Classify normalized binary pentanomials with a sparse seventh-power norm of odd weight.

Run with uv run --no-project --with python-flint==0.9.0 python scripts/check_seventh_power_supports.py.
"""

import argparse
from collections import Counter
from itertools import combinations, permutations
from math import gcd

from check_cubed_parity import X, polynomial, reciprocal
from check_cubing_chains import primitive
from power_images import classify_profile, norm_pattern, power_characteristic, residue_profiles


def in_family(points, residues):
    """Four points a,a+2u,a+3u,a+4u and a fifth b with u+2(b-a)=0 modulo seven."""
    doubled = {tuple(2*x for x in p): i for i, p in enumerate(points)}
    for i, j in permutations(range(5), 2):
        a = points[i]
        twice_u = tuple(y-x for x, y in zip(a, points[j]))
        k = doubled.get(tuple(2*x+3*d for x, d in zip(a, twice_u)))
        l = doubled.get(tuple(2*x+4*d for x, d in zip(a, twice_u)))
        if k is None or l is None:
            continue
        h, = set(range(5)) - {i, j, k, l}
        if (residues[j]-residues[i] + 4*(residues[h]-residues[i])) % 7 == 0:
            return True
    return False


def family_supports(n):
    """Place the endpoints zero and n to enumerate one degree without a search over triples."""
    out = set()

    def add(a, u, b):
        if gcd(u, b-a) != 1 or (u+2*(b-a)) % 7:
            return
        s = tuple(sorted({a, a+2*u, a+3*u, a+4*u, b}))
        if len(s) == 5:
            out.update((s, reciprocal(s)))

    # The isolated point is an endpoint, up to reciprocation.
    for k in range(1, (n-1)//4+1):
        add(0, k, n)
        add(4*k, -k, n)
    # Both endpoints belong to the progression, up to reciprocation.
    if n % 4 == 0:
        for b in range(1, n):
            add(0, n//4, b)
    return out


def direct(n):
    eligible = set()
    for taps in combinations(range(1, n), 3):
        if gcd(*taps, n) != 1:
            continue
        s = (0, *taps, n)
        image = power_characteristic(s, 7)
        if len(image) in (3, 5):
            eligible.add(s)
    return eligible


SOURCE_SHAPE = ((0, 0), (2, 0), (3, 0), (4, 0), (0, 1))
IMAGE_SHAPE = ((0, 0), (28, 0), (0, 7), (2, 4), (3, 6))


def normalized_degree(equations):
    """Degree of the normalized source on the common kernel of linear equations in (u,t)."""
    u, v = next((e for e in equations if e != (0, 0)), (0, 0))
    if (u, v) == (0, 0):
        raise ArithmeticError("the image meets the condition identically")
    if any(a*v-b*u for a, b in equations):
        return None
    source = [a*v-b*u for a, b in SOURCE_SHAPE]
    if len(set(source)) == 5:
        return (max(source)-min(source))//gcd(*source)
    return None


def check_second_image():
    collisions = {normalized_degree([tuple(x-y for x, y in zip(a, b))])
                  for a, b in combinations(IMAGE_SHAPE, 2)}
    aligned = set()
    for a, b, c, d in permutations(IMAGE_SHAPE, 4):
        equations = [tuple(x-3*y+2*z for x, y, z in zip(a, b, c)),
                     tuple(x-2*y+z for x, y, z in zip(a, b, d))]
        aligned.add(normalized_degree(equations))
    if collisions - {None} != {9, 12, 13, 25} or aligned - {None} != {8}:
        raise ArithmeticError("unexpected degrees for an image with collisions or four aligned terms")


def audit():
    exceptions = set()
    for residues in residue_profiles(7):
        if len(norm_pattern(7, residues)) % 2 == 0:
            continue
        sources = classify_profile(7, residues, in_family)
        if sources & exceptions:
            raise ArithmeticError("overlapping residue profiles")
        exceptions.update(sources)
        print("".join(map(str, residues)), len(sources), max((s[-1] for s in sources), default=0), flush=True)
    # For four aligned terms with a residue-compatible isolated point, the
    # identity of SeventhImage.lean has five surviving formal image terms.
    labels = (0, 2, 3, 4, 3)
    counts = Counter(tuple(sum(c*x for c, x in zip(mix, col)) for col in zip(*SOURCE_SHAPE))
                     for mix in norm_pattern(7, labels))
    if {p for p, c in counts.items() if c % 2} != set(IMAGE_SHAPE):
        raise ArithmeticError("the seventh-power family does not give a sparse norm")
    if len(exceptions) != 230 or max(s[-1] for s in exceptions) != 27:
        raise ArithmeticError("unexpected exceptional normalized supports")
    check_second_image()
    chains = Counter()
    for n in range(4, 28):
        family = family_supports(n)
        if any(not in_family([(e,) for e in s], [e % 7 for e in s]) for s in family):
            raise ArithmeticError("incorrect family support")
        sources = family | {s for s in exceptions if s[-1] == n}
        if direct(n) != sources:
            raise ArithmeticError(f"direct characteristic polynomials disagree in degree {n}")
        for s in sources | {(0, a, n) for a in range(1, n)}:
            if (primitive(polynomial(s), n) and len(power_characteristic(s, 7)) <= 5
                    and len(power_characteristic(s, 49)) <= 5):
                chains[n] += 1
    if chains != {4: 2, 5: 6, 6: 6, 7: 8, 8: 4, 9: 18, 10: 4}:
        raise ArithmeticError("unexpected sparse seventh-power chains")
    irr = [s for s in exceptions if polynomial(s).is_irreducible()]
    prim = [s for s in irr if primitive(polynomial(s), s[-1])]
    if (len(irr), len(prim), max(s[-1] for s in irr), max(s[-1] for s in prim)) != (111, 84, 25, 25):
        raise ArithmeticError("unexpected irreducible or primitive exceptions")
    print("One family and 230 exceptions. Outside the family 111 are irreducible, including 84 primitive.")
    return exceptions


def degree_sources(n):
    return family_supports(n) if n > 27 else direct(n)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="list eligible normalized supports in this degree")
    args = parser.parse_args()
    if args.degree is not None:
        if args.degree < 1:
            parser.error("degree must be positive")
        for s in sorted(degree_sources(args.degree)):
            print(*s)
    else:
        audit()
        candidates = degree_sources(1229)
        irr = sorted(s for s in candidates if polynomial(s).is_irreducible())
        source = (0, 166, 249, 332, 1229)
        target = polynomial((0, 332, 726, 1089, 1229))
        if irr != sorted((source, reciprocal(source))) or target.compose_mod(X**7, polynomial(source)) != 0:
            raise ArithmeticError("the degree-1229 pair failed")
        print(f"In degree 1229, exactly two of {len(candidates)} normalized supports are irreducible.")
