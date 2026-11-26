"""Recover individual projected logs from partly split binary norm-circle and trace-line equations."""

import argparse
import csv
from collections import Counter, defaultdict
from pathlib import Path

import numpy as np

from check_1229_circle_relations import MAPS, homogeneous, pairs
from check_1229_factor_base_orders import CIRCLE_LOGS, read_logs, read_table
from check_1229_isogeny_logs import H0, H1, Q, verify_powers
from check_1229_translated_circles import Constants, SIZE
from check_degree_1229 import COFACTOR
from check_factor_base import polynomial
from period_coordinate import mask_of


def binary_orbits(field, table):
    reps = np.flatnonzero(field.rep == field.elements)
    masks = np.zeros(SIZE, dtype=np.int32)
    for block in np.array_split(reps, 32):
        full = field.norm_polynomials(block)
        # For degree d < 20 the norm is the (20/d)-th power of the minimal polynomial.
        for i in np.flatnonzero(field.degree[block] != 20):
            (p, e), = polynomial(int(full[i])).factor()[1]
            if e*p.degree() != 20:
                raise ArithmeticError("invalid constant-field norm")
            full[i] = mask_of(p)
        masks[block] = full
    if set(map(int, masks[reps])) != table.keys():
        raise ArithmeticError("constant-field orbits differ from the verified table")
    return reps, masks


def left_logs(family, am, bm, field, reps, masks, table):
    # The binary irreducible for a finite point occurs once in the equation for its image.
    a = (reps if am & 2 else 0) ^ (am & 1)
    b = (reps if bm & 2 else np.zeros_like(reps)) ^ (bm & 1)
    finite = b != 0
    inverse = field.power[-field.log[b] % (SIZE-1)]
    t = field.multiply(a, inverse)
    eta = field.multiply(t, field.bar[t]) if family == "norm" else t ^ field.bar[t]
    grouped = defaultdict(int)
    for row, parameter in zip(masks[reps[finite]], masks[field.rep[eta[finite]]]):
        grouped[int(parameter)] += table[int(row)]
    return grouped


def rational_equations(table, field, reps, masks):
    parameters = sorted(p for p in table if 10 % (p.bit_length()-1) == 0)
    inverse_q = pow(Q, -1, COFACTOR)
    h1_log = table[2] + 2*table[3]
    for family, maps in MAPS.items():
        for am, bm in maps:
            grouped = left_logs(family, am, bm, field, reps, masks, table)
            a, b = polynomial(am), polynomial(bm)
            ah = int(a[1])*H0 + int(a[0])*H1
            bh = int(b[1])*H0 + int(b[0])*H1
            u, v = pairs(family, ah, a, bh, b)
            for p in parameters:
                if family == "norm" and p == 2:
                    continue
                d = p.bit_length()-1
                left = grouped[p]
                if family == "trace" and b.degree() == 1:
                    # Every projective trace line contains the pole of a/b.
                    left += d*table[bm]
                rhs = homogeneous(polynomial(p), u, v)
                parts = {mask_of(t): int(e) for t, e in rhs.factor()[1]}
                yield (inverse_q*left + d*h1_log) % COFACTOR, parts


def binary_norm(poly, degree, field):
    result = np.array([1], dtype=np.int32)
    for _ in range(degree):
        product = np.zeros(len(result)+len(poly)-1, dtype=np.int32)
        for i, c in enumerate(poly):
            if c:
                product[i:i+len(result)] ^= field.multiply(c, result)
        result = product
        poly = field.square[poly]
    if np.any(result > 1):
        raise ArithmeticError("a sextic norm has nonbinary coefficients")
    return polynomial(sum(int(c) << i for i, c in enumerate(result)))


def translated_equations(table, field, masks):
    # Enumerate conjugacy classes whose coefficients lie together in F_16 or F_32.
    seen = set()
    h1_log = table[2] + 2*table[3]
    inverse = pow(20*Q, -1, COFACTOR)
    for m in (4, 5):
        constants = np.flatnonzero(m % field.degree == 0)
        for b in constants:
            bar = field.bar[b]
            for d in constants[field.bar[constants] == constants]:
                radius = int(field.multiply(b, bar)) ^ int(d)
                if not radius or (b, d) in seen:
                    continue
                b1, d1 = b, d
                e = 0
                while (b1, d1) not in seen:
                    seen.add((b1, d1))
                    b1, d1 = field.square[b1], field.square[d1]
                    e += 1
                # (T+bar(b))*h0(T) + (b*T+d)*h1(T).
                sextic = np.array([bar, 1^d, bar^b, 1^d, b, bar, 1], dtype=np.int32)
                right = binary_norm(sextic, e, field)
                parts = {mask_of(t): int(mult) for t, mult in right.factor()[1]}
                points = field.circle_points(b, radius)
                counts = Counter(map(int, masks[field.rep[points]]))
                full_norm = sum(n*(20//(p.bit_length()-1))*table[p] for p, n in counts.items())
                yield e*(inverse*full_norm + h1_log) % COFACTOR, parts


def derive(table):
    known = dict(table)
    field = Constants()
    reps, masks = binary_orbits(field, table)
    pending = [*rational_equations(table, field, reps, masks), *translated_equations(table, field, masks)]
    total = len(pending)
    while True:
        next_round = []
        for rhs, factors in pending:
            missing = factors.keys() - known.keys()
            if len(missing) > 1:
                next_round.append((rhs, factors))
                continue
            residue = (rhs - sum(e*known[p] for p, e in factors.items() if p in known)) % COFACTOR
            if missing:
                p, = missing
                known[p] = residue * pow(factors[p], -1, COFACTOR) % COFACTOR
            elif residue:
                raise ArithmeticError("inconsistent circle relation")
        if len(next_round) == len(pending):
            break
        pending = next_round
    return total, {p: known[p] for p in known.keys()-table.keys()}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export", type=Path, help="write the new mask,exponent rows in decimal")
    parser.add_argument("--verify-powers", type=Path, help="check every new field power with NTL")
    parser.add_argument("--isogeny-logs", type=Path, help="also count the union with an exported isogeny table")
    args = parser.parse_args()
    modulus, table = read_table()
    count, extra = derive(table)
    if sorted(extra.items()) != list(read_logs(CIRCLE_LOGS)):
        raise ArithmeticError("the regenerated exponents differ from the published table")
    print(f"{count} equations recover {len(extra)} additional projected logarithms.", flush=True)
    print(f"Counts by binary degree: {dict(sorted(Counter(p.bit_length()-1 for p in extra).items()))}.", flush=True)
    if args.verify_powers:
        verify_powers(args.verify_powers, modulus, extra)
    if args.isogeny_logs:
        masks = set(table) | extra.keys()
        for p, _ in read_logs(args.isogeny_logs):
            if p in masks:
                raise ArithmeticError(f"overlapping or repeated isogeny mask {p:#x}")
            masks.add(p)
        print(f"The three tables contain {len(masks):,} distinct masks.")
    if args.export:
        with args.export.open("w", newline="") as stream:
            writer = csv.writer(stream, lineterminator="\n")
            writer.writerow(("mask", "exponent"))
            writer.writerows(sorted(extra.items()))
