"""Look up, reconstruct, or exhaustively audit the single-quadratic Hermitian pencils."""

import argparse
import csv
import gzip
import hashlib
import heapq
import json
import struct
import subprocess
import sys
import tempfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from itertools import islice
from math import prod
from pathlib import Path

from check_1229_factor_base_orders import read_table
from check_degree_1229 import COFACTOR, PRIMES
from check_factor_base import DATA, polynomial


CATALOGUE = DATA / "degree-1229-terminal-catalogue.bin.gz"
RECORD = struct.Struct("<QII")  # target mask, (A << 20) | b, d
TABLES = (
    ("scan", CATALOGUE, 1_187_645, "29381c1c041b5962852794d108bce5fb7eaf4b2177bfdb4117bf4345ca4b8804"),
    ("supplement", DATA / "degree-1229-terminal-conjugates.bin.gz", 26_362,
     "609e3b659ac59cd834cb6234e037a4a2eb5f045a396f354a08313a01f30bc0a2"),
)


def catalogue(path, count, digest):
    with gzip.open(path, "rb") as stream:
        data = stream.read()
    if len(data) != RECORD.size * count or hashlib.sha256(data).hexdigest() != digest:
        raise ValueError("terminal pencil catalogue length or digest differs")
    return data


def lookup(data, mask):
    lo, hi = 0, len(data)//RECORD.size
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


def rebuild(mode, data, backend, work, jobs):
    path = work / "pencils.txt"
    subprocess.run([str(backend.resolve()), mode, str(path)], check=True)
    seen = bytearray(len(data)//RECORD.size)
    with path.open() as stream, ThreadPoolExecutor(max_workers=jobs) as pool:
        for group in pool.map(lambda lines: native(backend, ["factor"], lines), batches(stream)):
            for p, a, b, d, mult, n, *roots in group:
                hit = lookup(data, p)
                simple = mode == "scan"
                expected_mult = 1 if simple else 40//(p.bit_length()-1)*2
                if (not hit or hit[1:] != ((a << 20) | b, d) or mult != expected_mult or n != (3 if simple else 1)+a
                        or len(roots) != n or seen[hit[0]]):
                    raise ArithmeticError("NTL factorization differs from the published catalogue")
                seen[hit[0]] = 1
    if not all(seen):
        raise ArithmeticError("some published quadratics were absent from the exhaustive search")
    print(f"Reconstructed all {len(seen):,} targets in {mode}.", file=sys.stderr)


def fiber_counts(rows, backend, jobs):
    counts = [Counter(), Counter(), Counter()]
    def traces(group):
        values = native(backend, ["traces"], [f"{p}\n" for p, _, _ in group])
        if [r[0] for r in values] != [p for p, _, _ in group]:
            raise ArithmeticError("incomplete relative-trace list")
        return values
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for values in pool.map(traces, batches(rows)):
            for p, *trace_masks in values:
                orbit = (p.bit_length()-1)//2
                for count, t in zip(counts, trace_masks, strict=True):
                    degree = t.bit_length()-1
                    if not degree or orbit % degree or 20 % degree:
                        raise ArithmeticError("incorrect binary degree of a fiber trace")
                    count[t] += orbit//degree
    for name, count, (limit, witness) in zip(("T", "1/T", "1/(T+1)"), counts,
            ((46, 0x41d), (45, 0x13d2b7), (52, 0x25)), strict=True):
        if (max(count.values()) != limit or count[witness] != limit or count[3] != 40 or
                sum((p.bit_length()-1)*n for p, n in count.items()) != 24_280_108):
            raise ArithmeticError(f"unexpected quadratic fibers in chart {name}")
        print(f"{name}: at most {limit} catalogue fibers at any fixed trace, attained at {witness:#x}. "
              f"Exactly {count[3]} have trace one.")


def order_census(stream):
    indices = Counter()
    minimum, maximum = 1230, 0
    lightest = []
    for line in stream:
        p, terms, missing = map(int, line.split())
        index = prod(prime for i, prime in enumerate(PRIMES) if missing >> i & 1)
        indices[index] += 1
        if terms < minimum:
            minimum, lightest = terms, []
        if terms == minimum:
            lightest.append(p)
        maximum = max(maximum, terms)
    return {"distinct": sum(indices.values()), "indices": {str(i): n for i, n in sorted(indices.items())},
            "minimum_terms": minimum, "minimum_masks": [hex(p) for p in sorted(lightest)],
            "maximum_terms": maximum}


def calculate(rows, backend, work, jobs, output, power_backend, check_individually, orders=False):
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
            return f"{a} {b} {d} 0 -1\n"
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
        writer = csv.writer(output, lineterminator="\n") if output else None
        if writer:
            writer.writerow(("mask", "exponent"))
        for group in pool.map(logarithms, batches(rows)):
            for p, e in group:
                if writer:
                    writer.writerow((hex(p), e))
                if power_backend:
                    print(p, e, file=verify)
    if orders:
        result = work / "orders.txt"
        with verification.open() as stream, result.open("w") as out:
            subprocess.run([str(power_backend.resolve()), "--extended"], stdin=stream, stdout=out, check=True)
        with result.open() as stream:
            return order_census(stream)
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
    select.add_argument("--orders", action="store_true", help="check all projected powers, full orders, and minimal-polynomial weights")
    select.add_argument("--fibers", action="store_true", help="count all catalogue fibers at a fixed trace in three projective coordinates")
    parser.add_argument("--backend", type=Path, help="compiled degree_1229_terminal_census executable")
    parser.add_argument("--power-backend", type=Path, help="independent census_1229_factor_base executable")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs <= 0 or (args.rebuild or args.export_all or args.fibers) and not args.backend:
        parser.error("use a positive job count and provide --backend for --rebuild, --export-all, or --fibers")
    if args.orders and not (args.backend and args.power_backend):
        parser.error("--orders requires --backend and --power-backend")
    if args.power_backend and not (args.export_all or args.mask or args.task or args.orders):
        parser.error("--power-backend requires a logarithm task")
    if args.power_backend and not args.backend:
        parser.error("--power-backend requires --backend to reconstruct the exponents")
    tables = {mode: catalogue(path, count, digest) for mode, path, count, digest in TABLES}
    if not (args.rebuild or args.mask or args.task or args.export_all or args.orders or args.fibers):
        print("1,214,007 distinct relative quadratics. The binary degrees are 40 for 1,214,005 and 8 for two.")
        return
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        if args.rebuild:
            for mode, data in tables.items():
                rebuild(mode, data, args.backend, work, args.jobs)
            return
        if args.fibers:
            fiber_counts(heapq.merge(*(RECORD.iter_unpack(data) for data in tables.values())), args.backend, args.jobs)
            return
        if args.orders:
            rows = heapq.merge(*(RECORD.iter_unpack(data) for data in tables.values()))
            summary = calculate(rows, args.backend, work, args.jobs, None, args.power_backend, False, orders=True)
            if summary != json.loads((DATA / "degree-1229-terminal-order-census.json").read_text()):
                raise ArithmeticError("order or weight census differs from the published result")
            print(json.dumps(summary, indent=2))
            return
        if args.export_all:
            # Complete a temporary file on the same filesystem before replacing an existing export.
            with tempfile.NamedTemporaryFile("w", dir=args.export_all.parent, delete=False) as output:
                path = Path(output.name)
                try:
                    rows = heapq.merge(*(RECORD.iter_unpack(data) for data in tables.values()))
                    calculate(rows, args.backend, work, args.jobs, output, args.power_backend, False)
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
            hits = [hit for data in tables.values() if (hit := lookup(data, p))]
            if hits:
                if len(hits) > 1:
                    raise ArithmeticError("a target appears in two pencil catalogues")
                rows.append((p, *hits[0][1:]))
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
