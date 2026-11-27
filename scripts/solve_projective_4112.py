"""Reconstruct the degree-4112 certificate by solving split-circle relations modulo B."""

import csv
import random
import sys

from gmpy2 import gcd, invert, mpz

from check_projective_4112 import B, K, Q, ConstantField, direction_orbits


def quadratic_roots(field, inverse_as, leading, middle, constant):
    """Return the roots with multiplicity, or None for an unusable numerator."""
    if leading == 0:
        if middle:
            return [field.divide(constant, middle)]
        return [] if constant else None
    if middle == 0:
        root = field.power(field.divide(constant, leading), K//2)
        return [root, root]
    normalized = field.divide(field.multiply(leading, constant), field.power(middle, 2))
    solution = inverse_as.get(normalized)
    if solution is None:
        return None
    scale = field.divide(middle, leading)
    return [field.multiply(scale, solution), field.multiply(scale, solution ^ 1)]


def circle_rows(field, orbits):
    locations = {c: (i, j) for i, orbit in enumerate(orbits) for j, c in enumerate(orbit)}
    powers = [pow(Q, j, B) for j in range(1 + max(map(len, orbits)))]
    offsets = [((Q**j - 1)//(Q-1)) % B for j in range(len(powers))]
    size = len(orbits)
    rows = []
    # The infinity orbit has representative logarithm zero. The last column
    # carries the affine constant, so a complete row evaluates to zero.
    for i, orbit in enumerate(orbits):
        row = [0] * size
        e = len(orbit)
        if i:
            row[i-1] = (powers[e]-1) % B
        row[-1] = offsets[e]
        if any(row):
            rows.append(row)

    def add_direction(row, c, sign):
        i, j = locations[c]
        if i:
            row[i-1] += sign * powers[j]
        row[-1] += sign * offsets[j]

    inverse_as = {field.power(t, 2) ^ t: t for t in range(K)}
    rng = random.Random(4112)
    tried = set()
    while len(rows) < 2*size + 7:
        center, h = rng.randrange(K), rng.randrange(Q-1)
        if (center, h) in tried:
            continue
        tried.add((center, h))
        radius = field.exp[h*(Q+1)]
        leading = 1 ^ field.power(center, Q)
        middle = 2 ^ field.multiply(center, leading) ^ radius
        roots = quadratic_roots(field, inverse_as, leading, middle, field.multiply(2, center))
        if roots is None:
            continue
        row = [0] * size
        row[-1] = 1  # the factor x clearing the Frobenius denominator
        for j in range(Q+1):
            c = center ^ field.exp[(h + (Q-1)*j) % (K-1)]
            add_direction(row, c, 1)
        for c in roots:
            add_direction(row, c, -1)
        rows.append([v % B for v in row])
    return rows


def solve(rows):
    modulus = mpz(B)
    matrix = [[mpz(x) for x in row] for row in rows]
    columns = len(matrix[0]) - 1
    for j in range(columns):
        pivot = next((i for i in range(j, len(matrix)) if gcd(matrix[i][j], modulus) == 1), None)
        if pivot is None:
            raise ValueError(f"no invertible pivot in column {j}")
        matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
        top = matrix[j]
        scale = invert(top[j], modulus)
        top[j:] = [x*scale % modulus for x in top[j:]]
        for row in matrix[j+1:]:
            multiple = row[j]
            if multiple:
                row[j:] = [(x-multiple*y) % modulus for x, y in zip(row[j:], top[j:])]
    values = [mpz(0)] * columns
    for j in reversed(range(columns)):
        row = matrix[j]
        values[j] = (-row[-1] - sum(x*y for x, y in zip(row[j+1:-1], values[j+1:]))) % modulus
    if any((row[-1] + sum(x*y for x, y in zip(row, values))) % modulus for row in rows):
        raise ValueError("inconsistent circle equations")
    return [0, *values]


if __name__ == "__main__":
    field = ConstantField()
    orbits = direction_orbits(field)
    values = solve(circle_rows(field, orbits))
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(("representative", "exponent"))
    writer.writerows((orbit[0], e) for orbit, e in zip(orbits, values, strict=True))
