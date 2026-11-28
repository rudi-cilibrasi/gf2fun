"""Classify sparse GF(4) factors of binary primitive trinomials and pentanomials.

The default run enumerates the possible exponent equalities over the rationals.
With --degree, test the two resulting families up to binary reciprocation using PARI/GP.
"""

import argparse
import json
import subprocess
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from math import gcd, lcm

import sympy as sp


def row_space(rows):
    if not rows:
        return ()
    reduced, pivots = sp.Matrix(rows).rref()
    return tuple(tuple(reduced.row(i)) for i in range(len(pivots)))


def positive_gaps(basis):
    """The nonnegative cone contains a positive point iff its rays cover every coordinate."""
    covered = set()
    for active in combinations(range(basis.rows), basis.cols - 1):
        kernel = basis[list(active), :].nullspace()
        if len(kernel) != 1:
            continue
        ray = basis * kernel[0]
        if min(ray) >= 0 or max(ray) <= 0:
            covered.update(i for i, value in enumerate(ray) if value)
    return len(covered) == basis.rows


def progression_model(points, colors):
    """Check the four evenly spaced terms symbolically in both reciprocal orientations."""
    reversed_points = [points[-1] - point for point in reversed(points)]
    reversed_colors = tuple((1 - color) % 3 for color in reversed(colors))
    for exponents, coefficients in ((points, colors), (reversed_points, reversed_colors)):
        for single in range(1, 5):
            ap = [j for j in range(5) if j != single]
            if tuple(coefficients[j] for j in ap) != (1, 1, 0, 0):
                continue
            if single == 4 and coefficients[single] != 0:
                continue
            step = exponents[ap[1]]  # The first exponent is zero.
            if all(exponents[j] == i * step for i, j in enumerate(ap)):
                return True
    return False


def classify(term_count):
    gaps = term_count - 1
    points = [sp.Matrix([[int(j < i) for j in range(gaps)]]) for i in range(term_count)]
    pairs = [(i, j, points[i] + points[j])
             for i, j in combinations_with_replacement(range(term_count), 2)]
    hyperplanes = set()
    for (_, _, left), (_, _, right) in combinations(pairs, 2):
        difference = tuple(left - right)
        if min(difference) < 0 < max(difference):
            hyperplanes.add(row_space([difference])[0])

    spaces = {()}
    layer = {()}
    for rank in range(1, gaps):
        layer = {space for rows in layer for h in hyperplanes
                 if len(space := row_space([*rows, h])) == rank}
        spaces.update(layer)

    counts = Counter()
    max_fixed_degree = 0
    for rows in spaces:
        matrix = sp.Matrix(rows) if rows else sp.zeros(0, gaps)
        basis = sp.Matrix.hstack(*matrix.nullspace())
        if not positive_gaps(basis):
            continue
        pair_sums = [(i, j, tuple(total * basis)) for i, j, total in pairs]
        for interior in product(range(3), repeat=term_count - 2):
            colors = (1, *interior, 0)  # Coefficient omega^c, normalized at both ends.
            multiplicities = Counter(colors)
            if len({multiplicities[c] % 2 for c in range(3)}) == 1:
                continue  # H(1) = 0 in GF(4).
            parity = Counter(value for i, j, value in pair_sums if i == j or colors[i] != colors[j])
            if sum(count % 2 for count in parity.values()) > 5:
                continue
            profile = tuple(sorted(multiplicities.values(), reverse=True))
            counts[basis.cols, profile] += 1
            if basis.cols == 1:
                direction = basis[:, 0]
                denominator = lcm(*(int(x.q) for x in direction))
                integers = [abs(int(x * denominator)) for x in direction]
                max_fixed_degree = max(max_fixed_degree, sum(integers) // gcd(*integers))
            elif profile == (3, 2):
                if not progression_model([point * basis for point in points], colors):
                    raise ArithmeticError(f'unclassified progression: {rows}, {colors}')
            elif profile != (term_count - 1, 1):
                raise ArithmeticError(f'unclassified coefficient pattern: {rows}, {colors}')
    return len(hyperplanes), len(spaces), max_fixed_degree, counts


def norm_families(degree):
    """All normalized supports in the two families, up to binary reciprocation."""
    half = degree // 2
    found = set()

    def add(terms):
        support = tuple(sorted(e for e, count in Counter(terms).items() if count % 2))
        if len(support) not in (3, 5) or support[0] != 0 or support[-1] != degree or gcd(*support) != 1:
            return
        reverse = tuple(degree - e for e in reversed(support))
        found.add(min(support, reverse))

    for i in range(1, 4):
        if degree % (1 << i):
            continue
        a = degree >> i
        for j in range(1, 5 - i):
            for b in range(1, ((degree - 1) >> j) + 1):
                add((0, a, degree, b, b << j))
    for b in range(1, (half - 1) // 3 + 1):
        add((0, 6*b, 2*half, half, half+b))
    if half % 3 == 0:
        b = half // 3
        for a in range(1, half):
            if a not in (b, 2*b):
                add((0, 6*b, 2*a, a, a+b))
    return sorted(found)


def audit_degree(degree, gp, orders):
    supports = norm_families(degree)
    procedure = """check(f,m,ord)={if(!polisirreducible(f), print(0); return());
      my(a=ffgen(f,'t), z=a^(2^m+1), p=minpoly(z));
      if(subst(p,variable(p),z)!=0, error("norm minimal polynomial"));
      print([fromdigits(lift(Vec(p)),2), if(ord,fforder(a),0)]);};"""
    calls = [f"check(Mod(1,2)*({'+'.join(f'x^{e}' for e in support)}),{degree//2},{int(orders)});"
             for support in supports]
    run = subprocess.run([gp, '-fq', '-s', '128M'], input='\n'.join([procedure, *calls, '']),
                         text=True, capture_output=True, check=True)
    if run.stderr:
        raise RuntimeError(run.stderr)
    irreducibles = []
    for support, line in zip(supports, run.stdout.splitlines(), strict=True):
        result = json.loads(line)
        if result:
            mask, order = result
            irreducibles.append((support, mask.bit_length()-1, mask.bit_count(), order))
    print(f'Degree {degree}: {len(supports)} candidates, {len(irreducibles)} irreducible reciprocal classes.')
    for support, norm_degree, weight, order in irreducibles:
        print(f'  {support}: norm minimal polynomial has degree {norm_degree} and weight {weight}.'
              + (f' Source order {order}.' if order else ''))
    if degree == 2458:
        expected = [((0, 910, 971, 1229, 2458), 1229, 631)]
        if len(supports) != 2558 or [row[:3] for row in irreducibles] != expected:
            raise ArithmeticError('degree-2458 census disagrees with the published result')
    if degree == 30 and orders:
        primitive = [s for s, _, _, order in irreducibles if order == 2**30 - 1]
        if primitive != [(0, 3, 6, 8, 30)]:
            raise ArithmeticError('degree-30 primitive classes disagree')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degree', type=int, help='enumerate one even degree greater than 16')
    parser.add_argument('--gp', default='gp', help='PARI/GP executable for a degree census')
    parser.add_argument('--orders', action='store_true', help='also compute root orders in the chosen degree')
    args = parser.parse_args()
    if args.degree is not None:
        if args.degree <= 16 or args.degree % 2:
            parser.error('--degree must be even and greater than 16')
        audit_degree(args.degree, args.gp, args.orders)
        return
    if args.orders:
        parser.error('--orders requires --degree')
    for terms in (4, 5):
        hyperplanes, spaces, maximum, counts = classify(terms)
        print(f'{terms} terms: {hyperplanes} hyperplanes, {spaces} row spaces, maximum degree on a ray {maximum}.')
        for (dimension, profile), count in sorted(counts.items()):
            print(f'  Dimension {dimension}, multiplicities {profile}: {count}')


if __name__ == '__main__':
    main()
