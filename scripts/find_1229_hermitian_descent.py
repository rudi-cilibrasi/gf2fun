"""Search Hermitian pencils for a binary mask of relative degree two or three."""

import argparse
import gzip
import json
import sys
from collections import Counter
from itertools import permutations, product
from pathlib import Path

import numpy as np

from check_1229_factor_base_orders import extended_table, read_table
from check_1229_hermitian_descent import (
    F, K, Q, binary_factors, bits, coefficient_norm, element, matrix,
    numerator, records, relation, scalar_groups,
)
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


def relative_factor(mask):
    if mask < 2 or not irreducible(polynomial(mask)):
        raise ValueError("choose a nonconstant binary irreducible mask")
    binary = K([mask >> i & 1 for i in range(mask.bit_length())])
    return min((p for p, _ in binary.factor()[1]), key=lambda p: tuple(bits(v) for v in p.coeffs()))


def search(mask):
    t = relative_factor(mask)
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
    best, counts = None, {1: Counter(), 2: Counter()}
    for h in candidates:
        a = matrix([element(v) for v in h])
        nonsingular_minor = any(not (a[i][i]*a[j][j]-a[i][j]*a[j][i]).is_zero()
                                for i in range(len(a)) for j in range(i))
        if not nonsingular_minor and len(a) != 2:
            continue
        rest, rem = divmod(numerator(a), t)
        if not rem.is_zero():
            raise ArithmeticError("a linear divisibility equation failed")
        largest = max((p.degree() for p, _ in rest.factor()[1]), default=0)
        counts[2 if nonsingular_minor else 1][largest] += 1
        row = {"mask_hex": hex(mask), "relative_factor": [bits(v) for v in t.coeffs()], "hermitian": h}
        if largest >= t.degree():
            if t.degree() != 2 or largest != 2:
                continue
            rhs = binary_factors(coefficient_norm(numerator(a)))
            partners = [p for p in rhs if p != mask and 20 % (p.bit_length()-1)]
            if len(partners) != 1 or rhs[partners[0]] != rhs[mask]:
                continue
            row["quadratic_partner_hex"] = hex(partners[0])
        score = len(relation(mask, row).keys()-known.keys())
        if best is None or (score, h) < best[:2]:
            best = (score, h, row)
    if counts[1]:
        print(f"Rank-one matrices by largest residual degree: {dict(sorted(counts[1].items()))}.", file=sys.stderr)
    print(f"Rank-two matrices by largest residual degree: {dict(sorted(counts[2].items()))}.", file=sys.stderr)
    return best and best[2]


def audit_cubics():
    count = 0
    for mask, row in records().items():
        if len(row["relative_factor"]) == 4:
            t = K([element(v) for v in row["relative_factor"]])
            basis = divisibility_space(t)
            if len(basis) != 3 or not smooth_plane(basis):
                raise ArithmeticError(f"failed determinant-plane check for {mask:#x}")
            count += 1
    print(f"Verified {count} smooth determinant cubics on three-dimensional divisibility spaces.")


def audit_quadratics(path):
    with (gzip.open(path, "rt") if path.suffix == ".gz" else path.open()) as stream:
        rows = json.load(stream)["remaining"]
    masks = [int(r["mask_hex"], 16) for r in rows]
    if len(set(masks)) != len(masks):
        raise ValueError("duplicate mask in the quadratic task")
    counts = Counter()
    for mask in masks:
        t = relative_factor(mask)
        if t.degree() != 2:
            raise ValueError(f"task row {mask:#x} has relative degree {t.degree()}")
        counts[len(divisibility_space(t))] += 1
    print(f"Quadratic masks by Hermitian nullity: {dict(sorted(counts.items()))}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("mask", nargs="?", type=lambda x: int(x, 0))
    modes.add_argument("--audit-cubics", action="store_true", help="check all published determinant planes")
    modes.add_argument("--audit-quadratics", type=Path, metavar="TASK",
                       help="count Hermitian nullities for the quadratic masks in a JSON or gzip task")
    args = parser.parse_args()
    try:
        if args.audit_cubics:
            audit_cubics()
        elif args.audit_quadratics:
            audit_quadratics(args.audit_quadratics)
        else:
            row = search(args.mask)
            if row is not None:
                print(json.dumps(row, indent=2))
    finally:
        # Drop FLINT elements while their finite-field context is still live.
        scalar_groups.cache_clear()


if __name__ == "__main__":
    main()
