"""Reconstruct all binomial logarithms by cubing and solving circle equations."""

import csv
import gzip
import json
import random
import sys

from check_4112_binomials import POWERS, expand, orbits
from check_4112_descent import DESCENT, M
from check_projective_4112 import B, K, Q, TABLE, ConstantField, direction_orbits
from solve_projective_4112 import quadratic_roots, solve_affine_rows


def initial_logarithms(field, record):
    with gzip.open(TABLE, "rt") as fp:
        values = {int(row["representative"]): int(row["exponent"]) for row in csv.DictReader(fp)}
    original = [0]*(K+1)
    for cycle in direction_orbits(field):
        start = values[cycle[0]]
        e = start
        for c in cycle:
            original[c] = e
            e = (Q*e + 1) % B
        if e != start:
            raise ValueError("the projective certificate does not close under Frobenius")

    alpha, beta = record["directions"]
    scale = record["scale"]
    numerator = field.multiply(scale, alpha)
    result = []
    for c in range(K):
        direction = K
        if c != scale:
            direction = field.divide(numerator ^ field.multiply(c, beta), scale ^ c)
        result.append((original[direction]-original[beta]) % B)
    return result


def solve_power(field, previous, cycles, unit, step, inverse_as):
    # A cube in the constant field has three roots there. Their three
    # linear factors in the preceding coordinate give an absolute logarithm.
    known = {}
    for i, cycle in enumerate(cycles):
        exponent = field.log[cycle[0]]
        if exponent % 3 == 0:
            known[i] = sum(previous[field.exp[exponent//3 + j*((K-1)//3)]]
                           for j in range(3)) % B
    free = [i for i in range(len(cycles)) if i not in known]
    columns = {cycle_id: j for j, cycle_id in enumerate(free)}
    locations = {c: (i, j) for i, cycle in enumerate(cycles) for j, c in enumerate(cycle)}
    frobenius = [pow(Q, i, B) for i in range(1 + max(map(len, cycles)))]
    size = len(free)

    def term(row, i, coefficient):
        if i in known:
            row[-1] += coefficient * known[i]
        else:
            row[columns[i]] += coefficient

    def direction(row, c, sign):
        if c:
            i, j = locations[c]
            term(row, i, sign*frobenius[j])

    rows = []
    for i, cycle in enumerate(cycles):
        row = [0]*(size+1)
        term(row, i, frobenius[len(cycle)]-1)
        row = [x % B for x in row]
        if any(row):
            rows.append(row)
    rng = random.Random(4112+step)
    while len(rows) < 2*size+15:
        center, h = rng.randrange(K), rng.randrange(Q-1)
        conjugate = field.power(center, Q)
        radius = field.exp[h*M]
        middle = unit ^ field.multiply(center, conjugate) ^ radius
        roots = quadratic_roots(field, inverse_as, conjugate, middle, field.multiply(center, unit))
        if roots is None:
            continue
        row = [0]*(size+1)
        for j in range(M):
            direction(row, center ^ field.exp[(h+(Q-1)*j) % (K-1)], 1)
        for c in roots:
            direction(row, c, -1)
        rows.append([x % B for x in row])

    values = solve_affine_rows(rows)
    return [known[i] if i in known else int(values[columns[i]]) for i in range(len(cycles))]


def reconstruct():
    field = ConstantField()
    record = json.loads(DESCENT.read_text())
    previous = initial_logarithms(field, record)
    inverse_as = {field.power(t, 2) ^ t: t for t in range(K)}
    result = {}
    for step, j in enumerate(POWERS):
        unit = field.power(record["unit"], j)
        cycles = orbits(field, unit)
        if step == 0:
            values = [previous[cycle[0]] for cycle in cycles]
        else:
            values = solve_power(field, previous, cycles, unit, step, inverse_as)
        rows = [(cycle[0], e) for cycle, e in zip(cycles, values, strict=True)]
        expanded = expand(rows, cycles)
        if step == 0 and previous != expanded:
            raise ValueError("initial chart does not match the certified projective logarithms")
        result[j], previous = rows, expanded
    return result


if __name__ == "__main__":
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(("power", "constant", "exponent"))
    for power, rows in reconstruct().items():
        writer.writerows((power, c, e) for c, e in rows)
