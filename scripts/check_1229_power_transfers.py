"""Search signed powers of every degree-1229 irreducible pentanomial for an order certificate."""

import argparse
import subprocess
import tempfile
from math import gcd
from pathlib import Path

from check_1229_factor_base_orders import extended_table, read_table
from check_1229_frobenius_models import power_basis_expression
from check_1229_power_images import SOURCE, TARGET
from check_1229_sparse_frobenius import support_table
from check_1229_terminal_census import RECORD, TABLES, catalogue
from check_degree_1229 import GROUP, N
from check_factor_base import modulus, polynomial
from period_coordinate import mask_of


def write_input(stream):
    field, logs = read_table()
    masks = set(extended_table(logs))
    for _, path, count, digest in TABLES:
        masks.update(p for p, _, _ in RECORD.iter_unpack(catalogue(path, count, digest)))
    supports = support_table().T
    print(field, len(masks), file=stream)
    for p in sorted(masks):
        print(p, file=stream)
    print(len(supports), file=stream)
    for a, b, c in supports:
        print(a, b, c, file=stream)
    if len(masks) != 1_304_685:
        raise ArithmeticError("incomplete union of reference tables")
    source_row = next(i for i, t in enumerate(supports) if tuple(t) == SOURCE)
    return field, masks, source_row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("backend", type=Path)
    parser.add_argument("--maximum", type=int, default=36869, help="largest odd exponent")
    parser.add_argument("--rows", type=int, nargs=2, metavar=("FIRST", "END"),
                        help="search only this zero-based half-open range of reciprocal pairs")
    args = parser.parse_args()
    if not 1 <= args.maximum < 36871 or args.maximum % 2 == 0:
        parser.error("choose an odd maximum between 1 and 36869")
    if any(gcd(m, GROUP) != 1 for m in range(1, args.maximum+1, 2)):
        raise ArithmeticError("a power can change the order")
    command = [str(args.backend.resolve()), str(args.maximum)]
    if args.rows:
        command.extend(map(str, args.rows))
    with tempfile.TemporaryFile(mode="w+") as stream:
        field, masks, source_row = write_input(stream)
        stream.seek(0)
        proc = subprocess.run(command, stdin=stream, text=True, stdout=subprocess.PIPE, check=True)
    x, model = polynomial(2), polynomial(field)
    hits = []
    for line in proc.stdout.splitlines():
        a, b, c, m, *target = line.split()
        taps, m = tuple(map(int, (a, b, c))), int(m)
        f = modulus(N, taps)
        if not 1 <= abs(m) <= args.maximum or m % 2 == 0:
            raise ValueError("invalid returned exponent")
        if target[0] == "mask":
            p = int(target[1])
            if len(target) != 2 or p not in masks:
                raise ValueError("unknown reference element")
            value = polynomial(p)
            leading = mask_of(value.pow_mod(N, model))
            image = x**N + power_basis_expression(p, leading, field)
            if image.compose_mod(value, model) != 0:
                raise ArithmeticError("incorrect reference minimal polynomial")
        else:
            image = modulus(N, tuple(map(int, target)))
        if image.compose_mod(x.pow_mod(m % GROUP, f), f) != 0:
            raise ArithmeticError("power substitution failed independent verification")
        hits.append((taps, m, tuple(target)))
        print(line)
    first, end = args.rows or (0, 319583)
    expected = [(SOURCE, 7, tuple(map(str, TARGET)))] if args.maximum >= 7 and first <= source_row < end else []
    if hits != expected:
        raise ArithmeticError(f"exact results differ from the published census: {hits}")
    print(f"Checked {2*(end-first)*((args.maximum+1)//2):,} oriented root powers "
          f"against {len(masks):,} reference elements.")


if __name__ == "__main__":
    main()
