"""Audit the ordinary-trinomial test for odd-degree product pentanomials."""

import argparse
import csv
from concurrent.futures import ProcessPoolExecutor
from functools import partial
from pathlib import Path

from flint import fmpz_poly, nmod_poly


X = nmod_poly([0, 1], 2)
Y = fmpz_poly([0, 1])
DATA = Path(__file__).resolve().parents[1] / "data"


def predicted_odd(n, u, v):
    a, b = (n-u-v)//2, (n-u)//2
    flip = False
    if b % 2:
        # The coefficient counts carry-free pairs i,j with a*i+b*j=u.
        for j in range(u//b+1):
            i, remainder = divmod(u-b*j, a)
            if remainder == 0 and i & j == 0:
                flip = not flip
        if 2*u < n:
            short = (u % a == 0) != (u >= b and (u-b) % (2*a) == 0)
            if short != flip:
                raise ArithmeticError(f"divisibility tests disagree at {(n, u, v)}")
    return (n % 8 in (1, 7)) != flip


def audit_tap(u, n, factor, integer):
    total = odd_count = small_total = small_odd = 0
    irreducibles = []
    for v in range(4, n-u, 4):
        odd = predicted_odd(n, u, v)
        total += 1
        odd_count += odd
        small_total += u < v
        small_odd += u < v and odd
        if factor:
            f = X**n + (1+X**u)*(1+X**v)
            factors = f.factor()[1]
            if any(e != 1 for _, e in factors) or len(factors) % 2 != odd:
                raise ArithmeticError(f"factor count disagrees at {(n, u, v)}")
            if len(factors) == 1:
                irreducibles.append((min(u, v), max(u, v)))
        if integer:
            f = Y**n + (1+Y**u)*(1+Y**v)
            if int(f.discriminant()) % 8 != (1 if odd else 5):
                raise ArithmeticError(f"integer discriminant disagrees at {(n, u, v)}")
    return total, odd_count, small_total, small_odd, irreducibles


def census(n, factor, integer, pool):
    check = partial(audit_tap, n=n, factor=factor, integer=integer)
    odd_taps = range(1, n-4, 2)
    rows = pool.map(check, odd_taps, chunksize=1) if pool else map(check, odd_taps)
    counts = [0, 0, 0, 0]
    hits = set()
    for *totals, irreducibles in rows:
        counts = [a+b for a, b in zip(counts, totals)]
        hits.update(irreducibles)
    return counts, hits


def published_supports(n):
    with (DATA / "open-product-irreducibles.csv").open(newline="") as stream:
        result = set()
        for row in csv.DictReader(stream):
            if int(row["degree"]) != n:
                continue
            u, v = int(row["u"]), int(row["v"])
            if (u % 2 and v % 4 == 0) or (v % 2 and u % 4 == 0):
                result.add((u, v))
        return result


def joint_counts(n):
    sieve = X
    cutoffs = []
    for d in range(1, 6):
        field = X**(2**d) + X
        sieve = (sieve//sieve.gcd(field))*field
        cutoffs.append(sieve)
    counts = [[0, 0] for _ in cutoffs]
    for u in range(1, n-4, 2):
        for v in range(4, n-u, 4):
            if not predicted_odd(n, u, v):
                continue
            f = X**n + (1+X**u)*(1+X**v)
            if f.gcd(f.reverse()) != 1:
                continue
            for row, small in zip(counts, cutoffs):
                if f.gcd(small) != 1:
                    break
                row[int(2*u >= n)] += 1
    for d, (lower, upper) in enumerate(counts, 1):
        print(f"Cutoff {d} and no inverse pair: {lower+upper:,} pass, including {lower:,} with 2u < n.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=80, help="check all odd degrees up to this limit")
    parser.add_argument("--degree", type=int, choices=[1229, 1231, 1237, 1243, 1249, 1259])
    parser.add_argument("--factor", action="store_true", help="factor every support in the selected large degree")
    parser.add_argument("--joint", action="store_true", help="count the joint survivors at cutoffs one through five")
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1 or args.through < 7:
        parser.error("expected a positive worker count and a small-degree limit of at least seven")
    if (args.factor or args.joint) and args.degree is None:
        parser.error("--factor and --joint require a selected large degree")
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        workers = pool if args.jobs > 1 else None
        if args.degree is None:
            total = sum(census(n, True, n <= 48, workers)[0][0] for n in range(7, args.through+1, 2))
            print(f"Verified factor counts for {total:,} supports through degree {args.through}.")
        else:
            n = args.degree
            counts, hits = census(n, args.factor, False, workers)
            published = published_supports(n)
            if args.factor and hits != published:
                raise ArithmeticError("direct factorization and published support list disagree")
            for u, v in published:
                if u % 2 == 0:
                    u, v = v, u
                if not predicted_odd(n, u, v):
                    raise ArithmeticError("published irreducible has incorrect predicted parity")
            print(f"Degree {n}: {counts[1]:,} odd among {counts[0]:,} supports, "
                  f"including {counts[3]:,} among {counts[2]:,} with the odd tap smaller. "
                  f"The complete support list contains {len(published)} irreducibles.")
            if args.joint:
                joint_counts(n)
