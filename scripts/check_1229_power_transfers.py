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


def write_supports(stream):
    supports = support_table().T
    print(len(supports), file=stream)
    for a, b, c in supports:
        print(a, b, c, file=stream)
    return supports


def write_input(stream):
    field, logs = read_table()
    masks = set(extended_table(logs))
    for _, path, count, digest in TABLES:
        masks.update(p for p, _, _ in RECORD.iter_unpack(catalogue(path, count, digest)))
    print(field, len(masks), file=stream)
    for p in sorted(masks):
        print(p, file=stream)
    supports = write_supports(stream)
    if len(masks) != 1_304_685:
        raise ArithmeticError("incomplete union of reference tables")
    source_row = next(i for i, t in enumerate(supports) if tuple(t) == SOURCE)
    return field, masks, source_row


def check_ratios(backend, maximum):
    with tempfile.TemporaryFile(mode="w+") as stream:
        supports = write_supports(stream)
        stream.seek(0)
        proc = subprocess.run([str(backend), str(maximum), "--sparse-ratios"], stdin=stream,
                              text=True, stdout=subprocess.PIPE, check=True)
    x = polynomial(2)
    hits = []
    for line in proc.stdout.splitlines():
        a, b, c, u, d, e, f, v = map(int, line.split())
        if not (0 < u <= maximum and 0 < abs(v) <= maximum and u % 2 and v % 2 and gcd(u, v) == 1):
            raise ValueError("invalid reduced ratio")
        left, right = modulus(N, (a, b, c)), modulus(N, (d, e, f))
        exponent = u*pow(v, -1, GROUP) % GROUP
        if right.compose_mod(x.pow_mod(exponent, left), left) != 0:
            raise ArithmeticError("rational power failed independent field substitution")
        hits.append(((a, b, c), u, (d, e, f), v))
        print(line)
    reciprocal = tuple(N-t for t in reversed(TARGET))
    expected = [(reciprocal, 1, SOURCE, -7)] if maximum >= 7 else []
    if maximum <= 1229 and hits != expected:
        raise ArithmeticError(f"reduced rational powers differ from the published census: {hits}")
    width = (maximum+1)//2
    print(f"Compared {len(supports)*width:,} classes up to squaring and inversion.")
    if maximum <= 1229:
        copies = (maximum//7+1)//2
        print(f"Their union contains {2*N*(len(supports)*width-copies):,} distinct field elements.")
        print(f"Any 21,305 reciprocal pairs give at least {2*N*(21305*width-copies):,} elements.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("backend", type=Path)
    parser.add_argument("--maximum", type=int, help="largest odd exponent (default 36869, or 1229 for ratios)")
    parser.add_argument("--sparse-ratios", action="store_true", help="compare powers on both sides of sparse pairs")
    parser.add_argument("--rows", type=int, nargs=2, metavar=("FIRST", "END"),
                        help="search only this zero-based half-open range of reciprocal pairs")
    args = parser.parse_args()
    if args.maximum is None:
        args.maximum = 1229 if args.sparse_ratios else 36869
    if not 1 <= args.maximum < 36871 or args.maximum % 2 == 0:
        parser.error("choose an odd maximum between 1 and 36869")
    if any(gcd(m, GROUP) != 1 for m in range(1, args.maximum+1, 2)):
        raise ArithmeticError("a power can change the order")
    if args.sparse_ratios:
        if args.rows:
            parser.error("the ratio comparison uses the full table of reciprocal pairs")
        check_ratios(args.backend.resolve(), args.maximum)
        return
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
