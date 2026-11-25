"""Audit the complete product-pentanomial tables for the six open degrees through 1280."""

import argparse
import csv
import json
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import cache
from math import gcd, prod
from pathlib import Path

from flint import fmpz, nmod_poly

from check_degree_1229 import COFACTOR, N, PRIMES


DATA = Path(__file__).resolve().parents[1] / "data"


@cache
def parameters():
    rows = json.loads((DATA / "open-degrees-1231-1259.json").read_text())
    return {N: (COFACTOR, list(PRIMES)), **{
        row["degree"]: (row["cofactor"], row["known_prime_factors"]) for row in rows}}


@cache
def tests(n):
    _, factors = parameters()[n]
    group = 2**n - 1
    degree_primes = [int(p) for p, _ in fmpz(n).factor()]
    projections = [group // p for p in sorted(set(factors))] + [prod(factors)]
    return group, [n // p for p in degree_primes if n // p > 1], projections


def verify_power(row):
    n, u, v, expected = row
    x = nmod_poly([0, 1], 2)
    f = x**n + (1 + x**u) * (1 + x**v)
    group, proper_degrees, projections = tests(n)
    # The full power implies squarefreeness and factor degrees dividing n.
    # f(0) = f(1) = 1 already excludes the linear factors.
    if x.pow_mod(group, f) != 1 or any(f.gcd(x.pow_mod(2**d, f) + x) != 1 for d in proper_degrees):
        raise ArithmeticError(f"irreducibility failed at degree {n}, taps {u}, {v}")
    mask = sum((x.pow_mod(e, f) == 1) << i for i, e in enumerate(projections))
    if mask != expected:
        raise ArithmeticError(f"incorrect projections at degree {n}, taps {u}, {v}")


def audit(jobs, selected):
    params = parameters()
    summary = {}
    with (DATA / "open-product-census.csv").open(newline="") as stream:
        reader = csv.reader(stream)
        fields = "degree supports squarefree reciprocal_free opposite_taps opposite_free irreducibles all_projections inside_known"
        if next(reader, None) != fields.split():
            raise ValueError("incorrect census header")
        for row in reader:
            n, supports, squarefree, free, opposite, both, irred, all_tests, inside = map(int, row)
            if (n in summary or n not in params or supports != (n//2)*(n//2-1)
                    or 2*opposite != supports or not 0 <= both <= min(free, opposite)
                    or not opposite <= squarefree <= supports or not irred <= free <= supports
                    or not 0 <= all_tests <= irred or not 0 <= inside <= irred):
                raise ValueError(f"inconsistent count row for degree {n}")
            summary[n] = irred, all_tests, inside
    if summary.keys() != params.keys():
        raise ValueError("missing degree totals")
    for n, (cofactor, factors) in params.items():
        k = prod(factors)
        if k * cofactor != 2**n - 1 or gcd(cofactor, k) != 1 or not all(fmpz(p).is_prime() for p in set(factors)):
            raise ArithmeticError(f"invalid group-order split in degree {n}")
    rows = []
    counts, passed, inside_known = Counter(), Counter(), Counter()
    previous = (0, 0, 0)
    with (DATA / "open-product-irreducibles.csv").open(newline="") as stream:
        reader = csv.reader(stream)
        if next(reader, None) != ["degree", "u", "v", "missing_mask"]:
            raise ValueError("incorrect support-list header")
        for entry in reader:
            n, u, v, mask = map(int, entry)
            if n not in params or not 0 < u < v < n-u or (n, u, v) <= previous:
                raise ValueError(f"invalid support at {entry}")
            last = len(set(params[n][1]))
            if not 0 <= mask < 1 << (last+1):
                raise ValueError(f"invalid projection mask at {entry}")
            previous = n, u, v
            counts[n] += 1
            passed[n] += mask == 0
            inside_known[n] += mask >> last
            if selected is None or n == selected:
                rows.append((n, u, v, mask))
    if any(summary[n] != (counts[n], passed[n], inside_known[n]) for n in params):
        raise ArithmeticError("support list and totals disagree")
    if jobs == 1:
        for row in rows:
            verify_power(row)
    else:
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            for _ in pool.map(verify_power, rows, chunksize=8):
                pass
    print(f"Verified irreducibility and every order projection for {len(rows):,} product pentanomials.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parameters", action="store_true", help="emit input for census_product_gaps.cpp")
    parser.add_argument("--degree", type=int, choices=sorted(parameters()), help="select a single degree")
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("expected a positive worker count")
    if args.parameters:
        for n, (cofactor, factors) in parameters().items():
            if args.degree is None or args.degree == n:
                print(n, cofactor, *sorted(factors))
    else:
        audit(args.jobs, args.degree)
