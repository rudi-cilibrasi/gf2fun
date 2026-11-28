"""Reconstruct candidate factorizations of 2^n-1 from the Mers Project archive."""

import argparse
import json
import re
import sys
from collections import defaultdict
from functools import cache
from math import gcd, isqrt, prod
from pathlib import Path

from flint import fmpz


def read_archive(path):
    factors = defaultdict(list)
    complete_parts = set()
    pattern = re.compile(r"M\(\s*(\d+)\s*\)([CDdS])(?:\s*:\s*(\d+))?")
    for line in path.read_text().splitlines():
        match = pattern.match(line)
        if match is None:
            continue
        n = int(match[1])
        if match[2] == "C":
            if match[3] is not None:
                factors[n].append(int(match[3]))
        else:
            # The completion marker only describes factors new at n.
            complete_parts.add(n)
    return factors, complete_parts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="Mers Project factoredM.txt")
    parser.add_argument("mersenne_primes", type=Path, help="Mers Project primeM.txt")
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--degrees", type=int, nargs="+", help="require every requested degree")
    target.add_argument("--range", type=int, nargs=2, metavar=("LOW", "HIGH"),
                        help="emit available factorizations in an inclusive interval")
    parser.add_argument("--supplement", action="append", type=Path, default=[],
                        help="factor map, Cunningham JSON, or witness table with order_factors")
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    new_factors, complete_parts = read_archive(args.archive)
    prime_exponents = {int(s) for s in args.mersenne_primes.read_text().split()}
    supplied = {}
    for path in args.supplement:
        table = json.loads(path.read_text())
        for degree, entry in table.get("table2-_data", table).items():
            if isinstance(entry, dict):
                entry = entry["order_factors"]
            supplied[int(degree)] = entry
    parents = {}
    for n in sorted(supplied):
        for d in range(2, isqrt(n) + 1):
            if n % d == 0:
                parents.setdefault(d, n)
                parents.setdefault(n // d, n)

    @cache
    def probable_prime(p):
        return p > 1 and bool(fmpz(p).is_probable_prime())

    @cache
    def reconstruct(n):
        if n == 1:
            return ()
        order = (1 << n) - 1
        if n in supplied:
            row = supplied[n]
            if prod(row) != order or not all(probable_prime(p) for p in row):
                raise ValueError(f"invalid supplementary factorization in degree {n}")
            return tuple(sorted(row))
        if n in prime_exponents:
            if not probable_prime(order):
                raise ValueError(f"composite number given as a Mersenne prime in degree {n}")
            return (order,)
        if n in parents:
            # A fully factored extension also supplies every prime of a subfield order.
            candidates = {p for p in reconstruct(parents[n]) if order % p == 0}
        elif n in complete_parts:
            candidates = set(new_factors[n])
            for p, _ in fmpz(n).factor():
                lower = reconstruct(n // int(p))
                if lower is None:
                    return None
                candidates.update(lower)
        else:
            return None
        remainder = order
        row = []
        for p in sorted(candidates):
            if order % p or not probable_prime(p):
                raise ValueError(f"invalid listed factor in degree {n}")
            while remainder % p == 0:
                row.append(p)
                remainder //= p
        if remainder > 1:
            parts = [remainder]
            if n % 8 == 4:
                # For odd m, 2^(2m)+1 = (2^m+1-2^((m+1)/2)) (2^m+1+2^((m+1)/2)).
                m = n // 4
                minus = (1 << m) + 1 - (1 << ((m + 1) // 2))
                left = gcd(minus, remainder)
                if 1 < left < remainder:
                    parts = [left, remainder // left]
            if not all(probable_prime(p) for p in parts):
                return None
            row.extend(parts)
        return tuple(sorted(row))

    if args.degrees:
        degrees = sorted(set(args.degrees))
        if degrees[0] < 2:
            parser.error("degrees must be at least two")
    else:
        low, high = args.range
        if not 2 <= low <= high:
            parser.error("expected 2 <= LOW <= HIGH")
        available = complete_parts | prime_exponents | supplied.keys() | parents.keys()
        degrees = sorted(n for n in available if low <= n <= high)
    rows = {}
    for n in degrees:
        row = reconstruct(n)
        if row is not None:
            rows[n] = row
        elif args.degrees:
            parser.error(f"incomplete archive factorization in degree {n}")
    print(json.dumps(rows, indent=2))


if __name__ == "__main__":
    main()
