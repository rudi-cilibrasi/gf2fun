"""Find product pentanomials with PARI/GP or verify a witness CSV with FLINT."""

import argparse
import csv
import json
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from functools import partial
from math import prod
from pathlib import Path

from flint import fmpz, nmod_poly


def search(row, least_span=False):
    gp, n, factors = row
    script = Path(__file__).with_name("search_product_range.gp")
    command = f"iferr(print(findproduct({n},{factors},{int(least_span)})), E, print(E); quit(1));\n"
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


def verify_batch(rows, primes):
    for row in rows:
        verify(*row)
    for p in primes:
        if not fmpz(p).is_prime():
            raise ValueError(f"composite order factor {p}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--factor-table", required=True, action="append", type=Path,
                        help="Cunningham table or degree-to-factor map, repeatable for supplements")
    parser.add_argument("--start", type=int, default=5)
    parser.add_argument("--end", type=int, required=True)
    parser.add_argument("--step", type=int, default=1, help="step between degrees, starting at --start")
    parser.add_argument("--available", action="store_true",
                        help="use precisely the degrees in the interval present in the factor table")
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--search", action="store_true", help="write the PARI search results as CSV")
    action.add_argument("--verify", type=Path, metavar="CSV", help="check each degree and prove its factors prime")
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for search")
    parser.add_argument("--least-span", action="store_true",
                        help="search in increasing u+v, breaking ties by u")
    parser.add_argument("--jobs", type=int, default=1, help="number of search or verification workers")
    args = parser.parse_args()
    if not 5 <= args.start <= args.end or min(args.step, args.jobs) < 1:
        parser.error("expected 5 <= start <= end and positive step and job counts")
    if args.least_span and not args.search:
        parser.error("--least-span applies to the search")
    table = {}
    for path in args.factor_table:
        with path.open() as source:
            part = json.load(source)
        part = part.get("table2-_data", part)
        for n in table.keys() & part.keys():
            if sorted(table[n]) != sorted(part[n]):
                raise ValueError(f"conflicting order factors in degree {n}")
        table.update(part)
    interval = range(args.start, args.end + 1, args.step)
    degrees = interval
    if args.available:
        degrees = [n for n in degrees if str(n) in table]
        if not degrees:
            parser.error("the factor table contains no degrees in the selected interval")
    factors = {n: table[str(n)] for n in degrees}
    for n, row in factors.items():
        if any(type(p) is not int or p < 2 for p in row) or prod(row) != 2**n - 1:
            raise ValueError(f"invalid factor list in degree {n}")

    if args.search:
        writer = csv.writer(sys.stdout, lineterminator="\n")
        writer.writerow(("degree", "u", "v"))
        with ThreadPoolExecutor(args.jobs) as pool:
            writer.writerows(pool.map(partial(search, least_span=args.least_span),
                                      ((args.gp, n, factors[n]) for n in degrees)))
        return

    entries = []
    with args.verify.open(newline="") as source:
        reader = csv.DictReader(source)
        if reader.fieldnames != ["degree", "u", "v"]:
            raise ValueError("expected CSV header degree,u,v")
        for n, row in zip(degrees, reader, strict=True):
            if int(row["degree"]) != n or None in row:
                raise ValueError(f"expected a single row for degree {n} in ascending order")
            entries.append((n, int(row["u"]), int(row["v"]), factors[n]))
    primes = sorted({p for row in factors.values() for p in row}, reverse=True)
    workers = min(args.jobs, len(entries))
    if workers == 1:
        verify_batch(entries, primes)
    else:
        with ProcessPoolExecutor(workers) as pool:
            checks = [pool.submit(verify_batch, entries[j::workers], primes[j::workers])
                      for j in range(workers)]
            for check in checks:
                check.result()
    print(f"Verified {len(degrees)} primitive product pentanomials in the interval "
          f"{args.start} through {args.end} and {len(primes)} distinct prime factors.")
    if args.available:
        missing = sorted(set(interval) - set(degrees))
        if missing:
            print("Degrees absent from the factor table: " + ", ".join(map(str, missing)) + ".")


if __name__ == "__main__":
    main()
