"""Find product pentanomials with PARI/GP or verify a consecutive CSV with FLINT."""

import argparse
import csv
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from math import prod
from pathlib import Path

from flint import fmpz, nmod_poly


def search(row):
    gp, n, factors = row
    script = Path(__file__).with_name("search_product_range.gp")
    command = f"iferr(print(findproduct({n},{factors})), E, print(E); quit(1));\n"
    result = subprocess.run([gp, "-fq", str(script)], input=command, text=True,
                            capture_output=True, check=False)
    if result.returncode or result.stderr:
        raise ValueError(f"PARI failed in degree {n}: {result.stdout}{result.stderr}")
    u, v = json.loads(result.stdout)
    return n, u, v


def verify(n, u, v, factors):
    if not 0 < u < v or u + v >= n:
        raise ValueError(f"invalid support in degree {n}")
    x = nmod_poly([0, 1], 2)
    f = x**n + x**(u+v) + x**v + x**u + 1
    order = 2**n - 1
    if x.pow_mod(order, f) != 1:
        raise ValueError(f"failed full power in degree {n}")
    for p in set(factors):
        if x.pow_mod(order // p, f) == 1:
            raise ValueError(f"index divisible by {p} in degree {n}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--factor-table", required=True, type=Path)
    parser.add_argument("--start", type=int, default=5)
    parser.add_argument("--end", type=int, required=True)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--search", action="store_true", help="write the PARI search results as CSV")
    action.add_argument("--verify", type=Path, metavar="CSV", help="check each degree and prove its factors prime")
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for search")
    parser.add_argument("--jobs", type=int, default=1, help="number of simultaneous PARI searches")
    args = parser.parse_args()
    if not 5 <= args.start <= args.end or args.jobs < 1:
        parser.error("expected 5 <= start <= end and at least one job")
    with args.factor_table.open() as source:
        table = json.load(source)
    table = table.get("table2-_data", table)
    degrees = range(args.start, args.end + 1)
    factors = {n: table[str(n)] for n in degrees}
    for n, row in factors.items():
        if any(type(p) is not int or p < 2 for p in row) or prod(row) != 2**n - 1:
            raise ValueError(f"invalid factor list in degree {n}")

    if args.search:
        writer = csv.writer(sys.stdout, lineterminator="\n")
        writer.writerow(("degree", "u", "v"))
        with ThreadPoolExecutor(args.jobs) as pool:
            writer.writerows(pool.map(search, ((args.gp, n, factors[n]) for n in degrees)))
        return

    with args.verify.open(newline="") as source:
        reader = csv.DictReader(source)
        if reader.fieldnames != ["degree", "u", "v"]:
            raise ValueError("expected CSV header degree,u,v")
        for n, row in zip(degrees, reader, strict=True):
            if int(row["degree"]) != n or None in row:
                raise ValueError(f"expected a single row for degree {n} in ascending order")
            verify(n, int(row["u"]), int(row["v"]), factors[n])
    primes = {p for row in factors.values() for p in row}
    for p in sorted(primes):
        if not fmpz(p).is_prime():
            raise ValueError(f"composite order factor {p}")
    print(f"Verified {len(degrees)} primitive product pentanomials, degrees "
          f"{args.start} through {args.end}, and {len(primes)} distinct prime factors.")


if __name__ == "__main__":
    main()
