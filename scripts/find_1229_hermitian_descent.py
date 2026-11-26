"""Search rank-two Hermitian pencils for a binary mask of relative degree two or three."""

import argparse
import json
import sys
from collections import Counter
from itertools import permutations, product

import numpy as np

from check_1229_factor_base_orders import extended_table, read_table
from check_1229_hermitian_descent import F, K, Q, bits, element, matrix, numerator, records, relation, scalar_groups
from check_1229_translated_circles import Constants
from check_factor_base import irreducible, polynomial


def nullspace(a, columns):
    pivots = []
    for col in range(columns):
        k = len(pivots)
        j = next((i for i in range(k, len(a)) if not a[i][col].is_zero()), None)
        if j is None:
            continue
        a[k], a[j] = a[j], a[k]
        a[k] = [v/a[k][col] for v in a[k]]
        for i, row in enumerate(a):
            if i != k and not row[col].is_zero():
                a[i] = [v-row[col]*w for v, w in zip(row, a[k])]
        pivots.append(col)
    basis = []
    for j in sorted(set(range(columns))-set(pivots)):
        row = [F.zero()]*columns
        row[j] = F.one()
        for i, col in enumerate(pivots):
            row[col] = -a[i][j]
        basis.append(row)
    return basis


def divisibility_space(t):
    n = t.degree()
    z = F.gen()
    entries = n*(n+1)//2
    units, cols = [], []
    for j in range(entries):
        for b in ([F.one()] if j < n else [F.one(), z]):
            unit = [F.zero()]*entries
            unit[j] = b
            residue = numerator(matrix(unit)) % t
            col = []
            for i in range(n):
                v = residue[i]
                second = (v+v**Q)/(z+z**Q)
                col.extend((v+second*z, second))
            cols.append(col)
            units.append(unit)
    coeffs = nullspace([list(r) for r in zip(*cols)], len(units))
    return [[sum((v*u[j] for v, u in zip(vector, units)), F.zero()) for j in range(entries)]
            for vector in coeffs]


def rank_two_plane(basis, field):
    """Enumerate P²(F_q) once, evaluating its cubic determinant in batches of q."""
    real = np.flatnonzero(field.bar == field.elements)
    mul = field.multiply
    def zeros(rows):
        a, b, c, u, v, w = rows
        cross = mul(mul(u, w), field.bar[v])
        det = (mul(a, mul(b, c) ^ mul(w, field.bar[w])) ^ mul(b, mul(v, field.bar[v]))
               ^ mul(c, mul(u, field.bar[u])) ^ cross ^ field.bar[cross])
        for i in np.flatnonzero(det == 0):
            yield rows[:, i].tolist()
    a, b, c = np.array([[bits(v) for v in row] for row in basis])
    line = mul(c[:, None], real[None, :])
    for s in real:
        yield from zeros((a ^ mul(b, s))[:, None] ^ line)
    yield from zeros(b[:, None] ^ line)
    yield from zeros(c[:, None])


def smooth_plane(basis):
    """Check that quadratic multiples of the three partials span all ternary quartics."""
    mats = [matrix(v) for v in basis]
    coeff = {}
    for s in permutations(range(3)):
        for i in range(3):
            for j in range(3):
                for k in range(3):
                    word = tuple(sorted((i, j, k)))
                    term = mats[i][0][s[0]]*mats[j][1][s[1]]*mats[k][2][s[2]]
                    coeff[word] = coeff.get(word, F.zero()) + term
    monomials = [tuple([0]*i + [1]*j + [2]*(4-i-j)) for i in range(5) for j in range(5-i)]
    rows = []
    for i in range(3):
        for j in range(3):
            for k in range(j, 3):
                row = dict.fromkeys(monomials, F.zero())
                for word, v in coeff.items():
                    if word.count(i) % 2:
                        reduced = list(word)
                        reduced.remove(i)
                        row[tuple(sorted((*reduced, j, k)))] += v
                rows.append([row[w] for w in monomials])
    return not nullspace(rows, len(monomials))


def circle_candidates(basis):
    """Choose the first nonzero coordinate to be one in each projective class."""
    _, real = scalar_groups()
    for i, lead in enumerate(basis):
        tail = basis[i+1:]
        for coeffs in product(real, repeat=len(tail)):
            yield [bits(v + sum((a*row[j] for a, row in zip(coeffs, tail)), F.zero()))
                   for j, v in enumerate(lead)]


def search(mask):
    if mask < 2 or not irreducible(polynomial(mask)):
        raise ValueError("choose a nonconstant binary irreducible mask")
    binary = K([mask >> i & 1 for i in range(mask.bit_length())])
    t = min((p for p, _ in binary.factor()[1]), key=lambda p: tuple(bits(v) for v in p.coeffs()))
    if t.degree() not in (2, 3):
        raise ValueError("choose a mask of relative degree two or three")
    basis = divisibility_space(t)
    print(f"Relative degree {t.degree()}, Hermitian nullity {len(basis)}.", file=sys.stderr)
    if t.degree() == 2:
        if not basis:
            return None
        candidates = circle_candidates(basis)
    else:
        if len(basis) != 3:
            raise ValueError("the divisibility conditions do not cut out a projective plane")
        print(f"Smooth determinant cubic: {smooth_plane(basis)}.", file=sys.stderr)
        candidates = rank_two_plane(basis, Constants())
    _, table = read_table()
    known = extended_table(table)
    known.update({p: int(row["log_mod_C"]) for p, row in records().items() if "log_mod_C" in row})
    best, counts = None, Counter()
    for h in candidates:
        a = matrix([element(v) for v in h])
        if not any(not (a[i][i]*a[j][j]-a[i][j]*a[j][i]).is_zero()
                   for i in range(len(a)) for j in range(i)):
            continue
        rest, rem = divmod(numerator(a), t)
        if not rem.is_zero():
            raise ArithmeticError("a linear divisibility equation failed")
        largest = max((p.degree() for p, _ in rest.factor()[1]), default=0)
        counts[largest] += 1
        if largest >= t.degree():
            continue
        row = {"mask_hex": hex(mask), "relative_factor": [bits(v) for v in t.coeffs()], "hermitian": h}
        score = len(relation(mask, row).keys()-known.keys())
        if best is None or (score, h) < best[:2]:
            best = (score, h, row)
    print(f"Rank-two matrices by largest residual degree: {dict(sorted(counts.items()))}.", file=sys.stderr)
    return best and best[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mask", type=lambda x: int(x, 0))
    args = parser.parse_args()
    try:
        row = search(args.mask)
    finally:
        # Drop FLINT elements while their finite-field context is still live.
        scalar_groups.cache_clear()
    if row is not None:
        print(json.dumps(row, indent=2))


if __name__ == "__main__":
    main()
