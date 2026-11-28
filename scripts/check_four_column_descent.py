"""Certify four-column Fourier minors over cyclotomic integers, then check the exceptional primes."""

from collections import Counter
from functools import cache
from itertools import combinations, permutations
from math import gcd, lcm, prod

from flint import fmpz, fmpz_poly


# d: (number of nonboundary intersections, norm primes congruent to 1 mod d,
#     normalized column pairs with zero determinant in the group algebra, per generator)
EXPECTED = {
    4: (214, {5: 0, 13: 4, 17: 0}),
    5: (238, {11: 0, 31: 0, 41: 0}),
    6: (230, {7: 0, 13: 0, 19: 0}),
    7: (238, {29: 0, 43: 0, 71: 0}),
}


def certify(d):
    cyclotomic = fmpz_poly.cyclotomic(d)
    variable = fmpz_poly([0, 1])
    zero = fmpz_poly()

    @cache
    def norm_of_coefficients(coefficients):
        return abs(int(cyclotomic.resultant(fmpz_poly(list(coefficients)))))

    def norm(a):
        return norm_of_coefficients(tuple(map(int, a)))

    def cross(a, b):
        return tuple((a[j]*b[k] - a[k]*b[j]) % cyclotomic for j, k in ((1, 2), (2, 0), (0, 1)))

    def dot(a, b):
        return sum((x*y for x, y in zip(a, b)), zero) % cyclotomic

    rows = [variable**i % cyclotomic for i in range(4)]
    # Translate the first column to zero. A permutation sum is then a linear
    # form in the three remaining columns.
    forms = [r[1:] for r in permutations(rows)]
    differences = [[tuple(x-y for x, y in zip(a, b)) for b in forms] for a in forms]
    boundaries = [(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, -1, 0), (1, 0, -1), (0, 1, -1)]
    exceptions = 1
    counts = Counter()
    for line in differences[0][1:]:
        if any(not any(cross(line, boundary)) for boundary in boundaries):
            # A nonzero coordinate of this line is a difference of distinct
            # row powers, so the line remains a boundary after specialization.
            counts['boundary lines'] += 1
            continue
        for k, comparisons in enumerate(differences):
            points = [cross(line, form) for j, form in enumerate(comparisons) if j != k]
            if all(any(point) for point in points):
                break
        else:
            raise ArithmeticError(f"no independent second comparison on line {line}")

        for point in points:
            # If two separate lines coincide modulo a prime, every coordinate
            # of their cross product reduces to zero at the chosen primitive root.
            exceptions = lcm(exceptions, gcd(*(norm(v) for v in point)))
            if any(not dot(point, boundary) for boundary in boundaries):
                counts['boundary intersections'] += 1
                continue
            values = [dot(point, form) for form in forms]
            multiplicity = Counter(tuple(map(int, v)) for v in values)
            obstruction = 0
            for k, value in enumerate(values):
                if multiplicity[tuple(map(int, value))] == 1:
                    obstruction = gcd(obstruction, prod(norm(value-v) for j, v in enumerate(values) if j != k))
                    if obstruction == 1:
                        break
            if not obstruction:
                raise ArithmeticError(f"no singleton at the characteristic-zero point {point}")
            exceptions = lcm(exceptions, obstruction)
            counts['nonboundary intersections'] += 1

    interior, expected = EXPECTED[d]
    if counts != {'boundary lines': 6, 'boundary intersections': 17*23-interior,
                  'nonboundary intersections': interior}:
        raise ArithmeticError(f"unexpected intersection counts for order {d}: {counts}")
    primes = {int(p) for p, _ in fmpz(exceptions).factor() if p % d == 1}
    if primes != expected.keys():
        raise ArithmeticError(f"unexpected exceptional characteristics: {primes}")
    for p in sorted(primes):
        generators = [u for u in range(2, p) if pow(u, d, p) == 1 and
                      all(pow(u, i, p) != 1 for i in range(1, d))]
        if not generators:
            raise ArithmeticError(f"no generator of order {d} modulo {p}")
        for u in generators:
            permuted = list(permutations(pow(u, i, p) for i in range(4)))
            vanished = 0
            for a, b in combinations(range(2, p), 2):
                frequencies = Counter((r[1] + a*r[2] + b*r[3]) % p for r in permuted)
                vanished += all(count % 2 == 0 for count in frequencies.values())
            if vanished != expected[p]:
                raise ArithmeticError(f"incorrect zero count at d={d}, p={p}, generator={u}")
    print(f"d={d}: {interior} nonboundary intersections, exceptional primes {sorted(primes)}, "
          f"group-algebra zero counts {list(expected.values())}.")


if __name__ == '__main__':
    for degree in EXPECTED:
        certify(degree)
