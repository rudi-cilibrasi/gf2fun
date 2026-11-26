"""Look up, reconstruct, or exhaustively audit the single-quadratic Hermitian pencils."""

import argparse
import csv
import gzip
import hashlib
import json
import struct
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from itertools import islice
from pathlib import Path

from check_1229_factor_base_orders import read_table
from check_degree_1229 import COFACTOR, PRIMES
from check_factor_base import DATA, polynomial


CATALOGUE = DATA / "degree-1229-terminal-catalogue.bin.gz"
RECORD = struct.Struct("<QII")  # target mask, (A << 20) | b, d
COUNT = 1_187_645
DIGEST = "29381c1c041b5962852794d108bce5fb7eaf4b2177bfdb4117bf4345ca4b8804"


def catalogue():
    with gzip.open(CATALOGUE, "rb") as stream:
        data = stream.read()
    if len(data) != RECORD.size * COUNT or hashlib.sha256(data).hexdigest() != DIGEST:
        raise ValueError("terminal pencil catalogue length or digest differs")
    return data


def lookup(data, mask):
    lo, hi = 0, COUNT
    while lo < hi:
        mid = (lo+hi)//2
        p, b, d = RECORD.unpack_from(data, mid*RECORD.size)
        if p == mask:
            return mid, b, d
        if p < mask:
            lo = mid+1
        else:
            hi = mid
    return None


def batches(rows, limit=8192):
    source = iter(rows)
    while batch := list(islice(source, limit)):
        yield batch


def native(backend, args, lines):
    result = subprocess.run([str(backend.resolve()), *args], input="".join(lines), text=True,
                            stdout=subprocess.PIPE, check=True)
    return [tuple(map(int, line.split())) for line in result.stdout.splitlines()]


def rebuild(data, backend, work, jobs):
    path = work / "pencils.txt"
    subprocess.run([str(backend.resolve()), "scan", str(path)], check=True)
    seen = bytearray(COUNT)
    with path.open() as stream, ThreadPoolExecutor(max_workers=jobs) as pool:
        for group in pool.map(lambda lines: native(backend, ["factor"], lines), batches(stream)):
            for p, a, b, d, mult, n, *roots in group:
                hit = lookup(data, p)
                if (not hit or hit[1:] != ((a << 20) | b, d) or mult != 1 or n != 3+a
                        or len(roots) != n or seen[hit[0]]):
                    raise ArithmeticError("NTL factorization differs from the published catalogue")
                seen[hit[0]] = 1
    if not all(seen):
        raise ArithmeticError("some published quadratics were absent from the exhaustive search")
    print(f"Reconstructed all {COUNT:,} distinct binary quadratic targets.", file=sys.stderr)


def calculate(rows, backend, work, jobs, output, power_backend, check_individually):
    field_mask, table = read_table()
    field = polynomial(field_mask)
    known = ((1 << 1229)-1)//COFACTOR
    base = polynomial(2).pow_mod(known, field)
    linear = work / "linear.txt"
    with linear.open("w") as stream:
        print(COFACTOR, file=stream)
        for p, e in table.items():
            print(p, e, file=stream)

    def logarithms(group):
        def parameter(packed, d):
            a, b = divmod(packed, 1 << 20)
            return f"{a} {b} {d} 20 {3+a}\n"
        result = native(backend, ["logs", str(linear)], [parameter(b, d) for _, b, d in group])
        if len(result) != len(group):
            raise ArithmeticError("incomplete terminal logarithm output")
        pairs = []
        for (mask, packed, radius), (p, a, b, d, e) in zip(group, result, strict=True):
            if (mask, packed, radius) != (p, (a << 20) | b, d) or not 0 <= e < COFACTOR:
                raise ArithmeticError("pencil or logarithm differs from the requested row")
            if check_individually and base.pow_mod(e, field) != polynomial(p).pow_mod(known, field):
                raise ArithmeticError(f"incorrect projected logarithm for {p:#x}")
            pairs.append((p, e))
        return pairs

    # The independent binary-field checker accepts the model and four primes followed by mask/exponent rows.
    verification = work / "powers.txt"
    with verification.open("w") as verify, ThreadPoolExecutor(max_workers=jobs) as pool:
        print(field_mask, *PRIMES, file=verify)
        writer = csv.writer(output, lineterminator="\n")
        writer.writerow(("mask", "exponent"))
        for group in pool.map(logarithms, batches(rows)):
            for p, e in group:
                writer.writerow((hex(p), e))
                if power_backend:
                    print(p, e, file=verify)
    if power_backend:
        with verification.open() as stream:
            subprocess.run([str(power_backend.resolve()), "--projected"], stdin=stream, stdout=sys.stderr, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    select = parser.add_mutually_exclusive_group()
    select.add_argument("--mask", type=lambda x: int(x, 0), action="append", help="look up one or more binary masks")
    select.add_argument("--task", type=Path, help="look up every remaining mask in a contributor task")
    select.add_argument("--rebuild", action="store_true", help="repeat the incidence census and all NTL factorizations")
    select.add_argument("--export-all", type=Path, help="reconstruct the entire mask,exponent CSV")
    parser.add_argument("--backend", type=Path, help="compiled degree_1229_terminal_census executable")
    parser.add_argument("--power-backend", type=Path, help="independent census_1229_factor_base executable")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs <= 0 or (args.rebuild or args.export_all) and not args.backend:
        parser.error("use a positive job count and provide --backend for --rebuild or --export-all")
    if args.power_backend and not (args.export_all or args.mask or args.task):
        parser.error("--power-backend requires a logarithm task")
    if args.power_backend and not args.backend:
        parser.error("--power-backend requires --backend to reconstruct the exponents")
    data = catalogue()
    if not (args.rebuild or args.mask or args.task or args.export_all):
        print(f"{COUNT:,} distinct relative quadratics, each of binary degree 40.")
        return
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        if args.rebuild:
            rebuild(data, args.backend, work, args.jobs)
            return
        if args.export_all:
            # Complete a temporary file on the same filesystem before replacing an existing export.
            with tempfile.NamedTemporaryFile("w", dir=args.export_all.parent, delete=False) as output:
                path = Path(output.name)
                try:
                    calculate(RECORD.iter_unpack(data), args.backend, work, args.jobs, output, args.power_backend, False)
                    output.close()
                    path.replace(args.export_all)
                finally:
                    path.unlink(missing_ok=True)
            return
        masks = args.mask
        if args.task:
            opener = gzip.open if args.task.suffix == ".gz" else open
            with opener(args.task, "rt") as stream:
                masks = [int(r["mask_hex"], 16) for r in json.load(stream)["remaining"]]
        rows = []
        for p in dict.fromkeys(masks):
            hit = lookup(data, p)
            if hit:
                rows.append((p, *hit[1:]))
            elif args.mask:
                print(f"{p:#x} has no pencil in the catalogue.", file=sys.stderr)
        print(f"{len(rows):,} of {len(masks):,} requested masks appear in the catalogue.", file=sys.stderr)
        if args.backend and rows:
            calculate(rows, args.backend, work, args.jobs, sys.stdout, args.power_backend, True)
        elif not args.backend:
            for p, packed, d in rows:
                a, b = divmod(packed, 1 << 20)
                print(f"{p:#x}  A={a}  b={b:#x}  d={d:#x}")


if __name__ == "__main__":
    main()
