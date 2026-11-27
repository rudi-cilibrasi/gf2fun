"""Check all possible coprime subfield products for sparse irreducibles of bounded odd degree."""

import argparse
import os
import subprocess
from concurrent.futures import ThreadPoolExecutor
from math import gcd, isqrt

from check_coprime_scalar_orders import survey


def cases(limit):
    _, scalars = survey(isqrt(limit))
    for i,h,_ in scalars:
        if i % 2 == 0:
            continue
        for j in range(i+2,limit//i+1,2):
            if gcd(i,j) == 1 and 9*i <= 4*j and 3*h <= i*j:
                yield i,j,h


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--products",required=True,help="compiled scripts/check_scalar_pair_products.cpp")
    parser.add_argument("--limit",type=int,default=2048)
    parser.add_argument("--jobs",type=int,default=1,help="number of degree pairs to check concurrently")
    parser.add_argument("--list",action="store_true",help="print every individual degree pair")
    args = parser.parse_args()
    if args.limit < 9 or args.jobs < 1:
        parser.error("expected a limit of at least nine and at least one worker")
    env = dict(os.environ)
    if args.jobs > 1:
        env.setdefault("OMP_NUM_THREADS","1")

    def check(row):
        result = subprocess.run([args.products,*map(str,row)],text=True,capture_output=True,env=env,check=True)
        counts = list(map(int,result.stdout.split()))
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
