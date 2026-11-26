"""Classify binary pentanomials whose cubed roots have a polynomial of odd weight at most five."""

import argparse
from collections import Counter
from functools import cache
from itertools import combinations, permutations, product
from math import gcd


# Each support is a translate of {i*u + j*v : (i,j) in the template}.
# Residues use the representatives (0,1), (1,1), (1,-1) up to simultaneous sign.
TEMPLATES = (
    (((0, 0), (1, 0), (2, 0), (3, 0), (0, 1)), (0, 1)),
    (((0, 0), (1, 0), (3, 0), (4, 0), (0, 1)), (1, -1)),
    (((0, 0), (1, 0), (2, 0), (0, 1), (0, 2)), (1, 1)),
    (((0, 0), (1, 0), (2, 0), (0, 1), (1, 1)), (1, -1)),
)
# With at least two residue classes and no primitive cube root of unity as a root,
# the class sizes are 4+1, 3+2 or 2+2+1. Translation and sign permute the residues.
RESIDUES = ((0, 0, 0, 0, 1), (0, 0, 0, 1, 1), (0, 0, 1, 1, 2))


def cubic_terms(points, residues):
    """Numerators of the exponents in A^3 + Y B^3 + Y^2 C^3 + Y A B C."""
    groups = [[p for p, r in zip(points, residues, strict=True) if r == i] for i in range(3)]
    terms = [tuple(2*x+y for x, y in zip(a, b)) for group in groups for a, b in product(group, repeat=2)]
    terms.extend(tuple(x+y+z for x, y, z in zip(a, b, c)) for a, b, c in product(*groups))
    return tuple(p for p, count in Counter(terms).items() if count % 2)


def cube_support(exponents):
    terms = cubic_terms([(e,) for e in exponents], [e % 3 for e in exponents])
    return tuple(sorted(x//3 for (x,) in terms))


def matches_residues(u, v, pair):
    return any((u-s*pair[0]) % 3 == (v-s*pair[1]) % 3 == 0 for s in (1, -1))


def in_template(points, residues):
    # The points at (0,0), (1,0), (0,1) determine a possible template.
    point_set = set(points)
    for origin, i, j in permutations(range(5), 3):
        a = points[origin]
        u = tuple(x-y for x, y in zip(points[i], a))
        v = tuple(x-y for x, y in zip(points[j], a))
        for shape, pair in TEMPLATES:
            if not matches_residues(residues[i]-residues[origin], residues[j]-residues[origin], pair):
                continue
            candidate = {tuple(t+k*x+l*y for t, x, y in zip(a, u, v)) for k, l in shape}
            if candidate == point_set:
                return True
    return False


def restrict(points, equation):
    """Impose one nonzero linear equation and clear a common denominator."""
    pivot = next(j for j, x in enumerate(equation) if x)
    scale = equation[pivot]
    projected = [tuple(scale*x - p[pivot]*c for j, (x, c) in enumerate(zip(p, equation)) if j != pivot)
                 for p in points]
    divisor = gcd(*(x for p in projected for x in p))
    # The surviving original coordinates have diagonal equal to the common scale.
    if scale < 0:
        divisor = -divisor
    return tuple(tuple(x//divisor for x in p) for p in projected)


def exceptional_supports(residues):
    exceptions = set()

    @cache
    def visit(points):
        if len(set(points)) != 5:
            return
        dimension = len(points[0])
        if dimension == 1:
            # The points are primitive integer coordinates on a line, up to common sign.
            if not any(all((s*p[0]-r) % 3 == 0 for p, r in zip(points, residues)) for s in (1, -1)):
                return
        terms = cubic_terms(points, residues)
        if len(terms) <= 5:
            if in_template(points, residues):
                return
            if dimension != 1:
                raise ArithmeticError(f"unclassified family for residue pattern {residues}: {points}")
            exponents = sorted(x for (x,) in points)
            for support in (exponents, [-x for x in reversed(exponents)]):
                exceptions.add(tuple(x-support[0] for x in support))
            return
        if dimension == 1:
            return
        # Any specialization with at most five survivors must identify at least
        # one of these six odd terms with another odd term.
        for i, term in enumerate(terms[:6]):
            for other in terms[i+1:]:
                equation = tuple(x-y for x, y in zip(term, other))
                visit(restrict(points, equation))

    initial = ((0, 0, 0, 0), *(tuple(int(i == j) for j in range(4)) for i in range(4)))
    visit(initial)
    visit.cache_clear()
    return exceptions


def classify():
    exceptions = set()
    for residues in RESIDUES:
        exceptions.update(exceptional_supports(residues))
    return exceptions


def step_pairs(n, dx, dy):
    """Integer solutions of dx*u + dy*v = n with |u|, |v| <= n."""
    if dy:
        for u in range(-n, n+1):
            rest = n-dx*u
            if rest % dy == 0 and abs(rest//dy) <= n:
                yield u, rest//dy
    elif n % dx == 0:
        for v in range(-n, n+1):
            yield n//dx, v


def degree_supports(n):
    if n <= 17:
        return {(0, *taps, n) for taps in combinations(range(1, n), 3)
                if gcd(*taps, n) == 1 and len(cube_support((0, *taps, n))) in (3, 5)}
    found = set()
    for shape, pair in TEMPLATES:
        # Choose which of the five positions is 0 and which is n.
        for (a, b), (c, d) in permutations(shape, 2):
            for u, v in step_pairs(n, c-a, d-b):
                if gcd(u, v) != 1 or not matches_residues(u, v, pair):
                    continue
                support = tuple(sorted((i-a)*u + (j-b)*v for i, j in shape))
                if support[0] == 0 and support[-1] == n and len(set(support)) == 5:
                    found.add(support)
    return found


def audit():
    exceptions = classify()
    # Independent direct enumeration in every exceptional degree.
    direct = {s for n in range(4, 18) for s in degree_supports(n)
              if not in_template([(x,) for x in s], [x % 3 for x in s])}
    if direct != exceptions or len(exceptions) != 130 or max(s[-1] for s in exceptions) != 17:
        raise ArithmeticError("the exceptional supports disagree with direct enumeration")
    for shape, residues in TEMPLATES:
        labels = [(i*residues[0]+j*residues[1]) % 3 for i, j in shape]
        if len(cubic_terms(shape, labels)) != 5:
            raise ArithmeticError("template does not give five formal image terms")
    return exceptions


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="list every normalized support in this degree and its cube image")
    parser.add_argument("--exceptions", action="store_true", help="print every exceptional support")
    args = parser.parse_args()
    if args.degree is not None:
        if args.degree < 1:
            parser.error("degree must be positive")
        for source in sorted(degree_supports(args.degree)):
            print(*source, "->", *cube_support(source))
    else:
        exceptional = audit()
        print(f"Four templates and {len(exceptional)} exceptional normalized supports, largest degree 17.")
        if args.exceptions:
            for source in sorted(exceptional, key=lambda s: (s[-1], s)):
                print(*source, "->", *cube_support(source))
