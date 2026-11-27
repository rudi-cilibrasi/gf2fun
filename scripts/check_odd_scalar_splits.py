"""Check all possible coprime subfield products for sparse irreducibles of bounded odd degree."""

import argparse
import csv
import os
import subprocess
from concurrent.futures import ThreadPoolExecutor
from functools import cache
from itertools import combinations
from math import comb, gcd, isqrt, prod
from pathlib import Path

from check_coprime_scalar_orders import survey
from check_scalar_order_bound import gcd_poly


def cases(limit):
    _, scalars = survey(isqrt(limit))
    for i,h,_ in scalars:
        if i % 2 == 0:
            continue
        for j in range(i+2,limit//i+1,2):
            if gcd(i,j) == 1 and 9*i <= 4*j and 3*h <= i*j:
                yield i,j,h


ARCHIVE_LIMIT = 2048
ARCHIVE = Path(__file__).resolve().parents[1] / "data" / "odd-scalar-splits-2048.csv"
COLUMNS = ("scalar_degree", "partner_degree", "scalar_order", "planes", "supports", "max_interior_gcd",
           "interior_singletons_with_factor", "endpoint_factor_occurrences", "split_supports")


@cache
def archived_planes(h, endpoint):
    # All archived scalar orders are prime, so the degree h-1 geometric sum is Phi_h.
    if h not in (7, 31, 73):
        raise ArithmeticError(f"unexpected archived scalar order {h}")
    cyclotomic = (1 << h) - 1
    return [(0, u, v) for u, v in combinations(range(1, h), 2)
            if endpoint in (0, u, v) and gcd_poly(cyclotomic, 1 | (1 << u) | (1 << v)) != 1]


def check_archived_counts(n, h):
    endpoint = n % h
    planes = archived_planes(h, endpoint)
    supports = 0
    for plane in planes:
        fixed = [int(r == 0) + int(r == endpoint) for r in plane]
        available = [(n-r)//h+1-used for r, used in zip(plane, fixed)]
        for singleton in plane:
            slots = [2-int(r == singleton)-used for r, used in zip(plane, fixed)]
            if min(slots) >= 0:
                supports += prod(comb(a, k) for a, k in zip(available, slots))
    return len(planes), supports


def read_archive():
    with ARCHIVE.open(newline="") as source:
        reader = csv.reader(source)
        if tuple(next(reader)) != COLUMNS:
            raise ValueError("incorrect census columns")
        archive = {}
        for entries in reader:
            row = tuple(map(int, entries))
            case = row[:3]
            if len(row) != len(COLUMNS) or case in archive:
                raise ValueError(f"invalid census row for {case}")
            archive[case] = row[3:]
    if set(archive) != set(cases(ARCHIVE_LIMIT)):
        raise ArithmeticError("the archived degree pairs are incomplete")
    return archive


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--products", help="compiled scripts/check_scalar_pair_products.cpp")
    mode.add_argument("--check-counts", action="store_true", help="reconstruct archived support counts using binomial coefficients")
    parser.add_argument("--limit",type=int,default=2048)
    parser.add_argument("--jobs",type=int,default=1,help="number of degree pairs to check concurrently")
    parser.add_argument("--list",action="store_true",help="print every individual degree pair")
    args = parser.parse_args()
    if args.limit < 9 or args.jobs < 1:
        parser.error("expected a limit of at least nine and at least one worker")
    archive = read_archive()
    if args.check_counts:
        if args.limit > ARCHIVE_LIMIT:
            parser.error(f"archived counts run through degree {ARCHIVE_LIMIT}")
        total = tests = 0
        for case in cases(args.limit):
            i, j, h = case
            counts = check_archived_counts(i*j, h)
            if counts != archive[case][:2]:
                raise ArithmeticError(f"support count disagrees for {case}")
            if args.list:
                print(*case, *counts)
            tests += 1
            total += counts[1]
        print(f"Reconstructed {total:,} candidate supports across {tests} archived scalar cases.")
        return
    env = dict(os.environ)
    if args.jobs > 1:
        env.setdefault("OMP_NUM_THREADS","1")

    def check(row):
        result = subprocess.run([args.products,*map(str,row)],text=True,capture_output=True,env=env,check=True)
        counts = list(map(int,result.stdout.split()))
        if row in archive and tuple(counts) != archive[row]:
            raise ArithmeticError(f"polynomial census differs from the archive for {row}")
        if len(counts) != 6:
            raise ArithmeticError(f"incorrect scalar census output for {row}")
        return row,counts

    tests = supports = splits = 0
    degrees = set()
    with ThreadPoolExecutor(args.jobs) as pool:
        for row,counts in pool.map(check,cases(args.limit)):
            degrees.add(row[0] * row[1])
            tests += 1
            supports += counts[1]
            splits += counts[-1]
            if counts[-1] or args.list:
                print(*row,*counts,flush=True)
    summary = tests, len(degrees), supports, splits
    expected = {1200: (257, 230, 725361232, 0), 2048: (450, 404, 6226592338, 0)}
    if args.limit in expected and summary != expected[args.limit]:
        raise ArithmeticError(f"unexpected counts through degree {args.limit}: {summary}")
    print(f"Odd degrees through {args.limit}: {tests} scalar cases in {len(degrees)} degrees, "
          f"{supports:,} supports, {splits} splits.")


if __name__ == "__main__":
    main()
