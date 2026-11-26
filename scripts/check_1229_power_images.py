"""Census fifth and seventh powers of roots of irreducible degree-1229 pentanomials.

Run with uv run --no-project --with numpy --with python-flint==0.9.0 python
scripts/check_1229_power_images.py. The logarithm options need only FLINT.
"""

import argparse
import json
from collections import Counter
from math import gcd
from pathlib import Path

from check_1229_frobenius_models import primitive_generator_in
from check_1229_sparse_frobenius import support_table
from check_degree_1229 import COFACTOR, GROUP, KNOWN, N, check_known_order
from check_factor_base import DATA, irreducible, modulus, polynomial
from period_coordinate import mask_of
from power_images import norm_pattern


SOURCE = (166, 249, 332)
TARGET = (332, 726, 1089)


def census(m, taps):
    import numpy as np
    if gcd(m, GROUP) != 1:
        raise ArithmeticError("powering could shorten the Frobenius orbit")
    a, b, c = taps
    tags = ((a % m)*m + b % m)*m + c % m
    ordering = np.argsort(tags, kind="stable")
    groups = np.split(ordering, np.flatnonzero(np.diff(tags[ordering])) + 1)
    counts = Counter()
    minimum, witnesses = N+1, []
    for indices in groups:
        supports = np.column_stack((np.zeros_like(indices), taps[:, indices].T,
                                    np.full_like(indices, N))).astype(np.int32)
        residues = supports[0] % m
        perm = np.argsort(residues, kind="stable")
        pattern = np.array(norm_pattern(m, tuple(map(int, residues[perm]))), dtype=np.int32)
        exponents = (supports[:, perm] @ pattern.T) // m
        parity = np.zeros((len(indices), N+1), dtype=np.uint8)
        np.bitwise_xor.at(parity, (np.arange(len(indices))[:, None], exponents), 1)
        weights = np.count_nonzero(parity, axis=1)
        for w, count in zip(*np.unique(weights, return_counts=True)):
            counts[int(w)] += 2*int(count)
        small = int(weights.min())
        if small < minimum:
            minimum, witnesses = small, []
        if small == minimum:
            for i in np.flatnonzero(weights == small):
                witnesses.append((tuple(map(int, supports[i, 1:4])),
                                  tuple(map(int, np.flatnonzero(parity[i])))))
    if sum(counts.values()) != 639166 or counts[minimum] != 2*len(witnesses):
        raise ArithmeticError("incomplete census")
    # Check each extremal image again by direct composition in the source field.
    x = polynomial(2)
    for taps, powers in witnesses:
        f = modulus(N, taps)
        g = polynomial(sum(1 << e for e in powers))
        if g.degree() != N or g.compose_mod(x**m, f) != 0:
            raise ArithmeticError("an extremal image fails direct substitution")
    return minimum, sorted(witnesses), counts


def verify_pair():
    x = polynomial(2)
    f, g = modulus(N, SOURCE), modulus(N, TARGET)
    if not irreducible(f) or not irreducible(g) or g.compose_mod(x**7, f) != 0:
        raise ArithmeticError("the seventh-power map fails")
    if x.pow_mod(7*pow(7, -1, GROUP), f) != x:
        raise ArithmeticError("seventh powering did not invert")
    for h in (f, g):
        check_known_order(h)
    return f


def split_task(row, logs=None):
    from check_1229_factor_base_orders import DIRECTION_LOGS, extended_table, read_logs, read_table
    from check_1229_hermitian_descent import bits, records, relative_factor
    from check_1229_log_descent import checked_exponent, reduce_task, sparse_quotient
    from check_1229_norm_height import checked_norm
    from prepare_1229_single_log import prepare

    if tuple(row["source_taps"]) != SOURCE:
        raise ValueError("incorrect sparse source in the split")
    _, field, _, root = prepare(SOURCE)
    field_mask, table = read_table()
    if mask_of(field) != field_mask:
        raise ValueError("the sparse root uses a different logarithm basis")
    j, shift = row["frobenius"], row["base_shift"]
    if not 0 <= j < N or not 0 <= shift < GROUP:
        raise ValueError("invalid Frobenius index or base shift")
    x = polynomial(2)
    base = x.pow_mod(KNOWN, field)
    conjugate = root.pow_mod(1 << j, field) * x.pow_mod(shift, field) % field
    relation = sparse_quotient(conjugate, row, field)
    relation[2] -= shift
    inverse = pow(1 << j, -1, COFACTOR)
    coefficients = {p: inverse*c for p, c in relation.items() if c}

    table = extended_table(table)
    table.update(read_logs(DIRECTION_LOGS))
    table.update({p: int(r["log_mod_C"]) for p, r in records().items() if "log_mod_C" in r})
    known = {p: checked_exponent(p, table[p], base, field) for p in coefficients.keys() & table.keys()}
    masks = coefficients.keys()-known.keys()
    if "logarithms" in row:
        entries = row["logarithms"]["remaining"]
        pieces = {int(p["mask_hex"], 16): p for p in entries}
        if pieces.keys() != masks or len(pieces) != len(entries):
            raise ArithmeticError("the supplied relative factors do not cover the unsolved masks")
    else:
        pieces = {p: {"mask_hex": hex(p), "norm_multiplicity": 20//gcd(p.bit_length()-1, 20),
                      "relative_factor": [bits(c) for c in relative_factor(p).coeffs()]} for p in masks}
    for mask, piece in pieces.items():
        d = mask.bit_length()-1
        if piece["norm_multiplicity"] != 20//gcd(d, 20):
            raise ArithmeticError("incorrect coefficient-norm multiplicity")
        checked_norm(piece, d//gcd(d, 20), piece["norm_multiplicity"])
    task = reduce_task("seventh-power", root, coefficients, known, base, field, logs)
    for item in task["remaining"]:
        piece = pieces[int(item["mask_hex"], 16)]
        item.update(relative_factor=piece["relative_factor"], norm_multiplicity=piece["norm_multiplicity"])
    if not task["remaining"]:
        task["exact_index"] = str(gcd(int(task["known_exponent_mod_C"]), COFACTOR))
    return task


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    options = parser.add_mutually_exclusive_group()
    options.add_argument("--task", action="store_true", help="export the common-index logarithm task")
    options.add_argument("--log", type=int, metavar="EXPONENT", help="verify the common-index logarithm")
    options.add_argument("--split", nargs="?", type=int, choices=(6, 9), const=9,
                         help="export a split into 6 or 9 factor logarithms (default with --split: 9)")
    options.add_argument("--check-split", type=Path, help="verify a finder row and export its individual logarithms")
    parser.add_argument("--logs", type=Path, help="check a partial or complete mask,exponent CSV for a split")
    args = parser.parse_args()
    if args.logs and not (args.split or args.check_split):
        parser.error("--logs requires --split or --check-split")
    f = verify_pair()
    if args.split or args.check_split:
        if args.check_split:
            row = {"source_taps": list(SOURCE), **json.loads(args.check_split.read_text())}
        else:
            filename = ("degree-1229-seventh-power-split-six.json" if args.split == 6
                        else "degree-1229-seventh-power-split.json")
            row = json.loads((DATA / filename).read_text())
            if len(row["logarithms"]["remaining"]) != args.split:
                raise ArithmeticError("unexpected number of factor tasks")
        task = split_task(row, args.logs)
        if not args.logs and "logarithms" in row and task != row["logarithms"]:
            raise ArithmeticError("the published logarithm split differs from the field calculation")
        print(json.dumps(row | {"logarithms": task} if args.check_split and not args.logs else task, indent=2))
        return
    if args.task or args.log is not None:
        base = primitive_generator_in(f).pow_mod(KNOWN, f)
        target = polynomial(2).pow_mod(KNOWN, f)
        if args.task:
            print(json.dumps({"source_taps": SOURCE, "seventh_power_taps": TARGET,
                              "field_modulus_hex": hex(mask_of(f)), "K": str(KNOWN), "C": str(COFACTOR),
                              "base_hex": hex(mask_of(base)), "target_hex": hex(mask_of(target))}, indent=2))
        else:
            if not 0 <= args.log < COFACTOR or base.pow_mod(args.log, f) != target:
                raise ValueError("the submitted logarithm fails direct powering")
            print(f"All four pentanomials have exact root index {gcd(args.log, COFACTOR)}.")
        return

    taps = support_table()
    for m, expected, count in ((5, 9, 14), (7, 5, 2)):
        minimum, witnesses, counts = census(m, taps)
        if (minimum, counts[minimum]) != (expected, count):
            raise ArithmeticError("unexpected minimum weight or multiplicity")
        if m == 7 and witnesses != [(SOURCE, (0, *TARGET, N))]:
            raise ArithmeticError("unexpected seventh-power pair")
        print(f"Power {m} across {sum(counts.values())} polynomials: "
              f"minimum weight {minimum}, attained by {count} sources including reciprocals.")


if __name__ == "__main__":
    main()
