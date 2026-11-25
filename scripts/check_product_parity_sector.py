"""Audit the ordinary-trinomial test for odd-degree product pentanomials."""

import argparse
import csv
from concurrent.futures import ProcessPoolExecutor
from functools import partial
from itertools import chain
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


def even_taps(n, u, sector):
    multiples_of_four = range(4, n-u, 4)
    if sector == "four":
        return multiples_of_four
    if sector == "smaller":
        return range(u+1, n-u, 2)
    first = u+1+(1-u) % 4
    twice_odd = range(first, n-u, 4)
    if sector == "two-smaller":
        return twice_odd
    return chain(multiples_of_four, twice_odd)


def sector_odd(n, u, v):
    if v % 4 == 0:
        return predicted_odd(n, u, v)
    if not u < v:
        raise ValueError("the even tap must exceed the odd tap in this sector")
    a, b, r = (n-u-v)//2, (n-u)//2, v//2
    divisors = sum((n-j*u) % r == 0 for j in range(4))
    if b % 2 == 0:
        divisors += (u % a == 0) + int(u >= a+b and (u-a-b) % (2*a) == 0)
    return (n % 8 in (1, 7)) != bool(divisors % 2)


def audit_tap(u, n, factor, integer, sector):
    total = odd_count = small_total = small_odd = 0
    irreducibles = []
    for v in even_taps(n, u, sector):
        odd = sector_odd(n, u, v)
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


def census(n, factor, integer, pool, sector):
    check = partial(audit_tap, n=n, factor=factor, integer=integer, sector=sector)
    odd_taps = range(1, n-2, 2)
    rows = pool.map(check, odd_taps, chunksize=1) if pool else map(check, odd_taps)
    counts = [0, 0, 0, 0]
    hits = set()
    for *totals, irreducibles in rows:
        counts = [a+b for a, b in zip(counts, totals)]
        hits.update(irreducibles)
    return counts, hits


def published_supports(n, sector):
    with (DATA / "open-product-irreducibles.csv").open(newline="") as stream:
        result = set()
        for row in csv.DictReader(stream):
            if int(row["degree"]) != n:
                continue
            u, v = int(row["u"]), int(row["v"])
            four = (u % 2 and v % 4 == 0) or (v % 2 and u % 4 == 0)
            smaller = u % 2 == 1 and v % 2 == 0
            selected = {"four": four, "smaller": smaller, "two-smaller": smaller and v % 4 == 2,
                        "union": four or smaller}
            if selected[sector]:
                result.add((u, v))
        return result


def joint_counts(n, sector):
    sieve = X
    cutoffs = []
    for d in range(1, 6):
        field = X**(2**d) + X
        sieve = (sieve//sieve.gcd(field))*field
        cutoffs.append(sieve)
    counts = [[0, 0] for _ in cutoffs]
    for u in range(1, n-2, 2):
        for v in even_taps(n, u, sector):
            if not sector_odd(n, u, v):
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
    parser.add_argument("--sector", choices=["four", "smaller", "two-smaller", "union"], default="four",
                        help="the multiple-of-four sector, the odd-smaller sector, its added part, or their union")
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
            total = sum(census(n, True, n <= 48, workers, args.sector)[0][0]
                        for n in range(7, args.through+1, 2))
            print(f"Verified factor counts for {total:,} supports through degree {args.through}.")
        else:
            n = args.degree
            counts, hits = census(n, args.factor, False, workers, args.sector)
            published = published_supports(n, args.sector)
            if args.factor and hits != published:
                raise ArithmeticError("direct factorization and published support list disagree")
            for u, v in published:
                if u % 2 == 0:
                    u, v = v, u
                if not sector_odd(n, u, v):
                    raise ArithmeticError("published irreducible has incorrect predicted parity")
            print(f"Degree {n}: {counts[1]:,} odd among {counts[0]:,} supports, "
                  f"including {counts[3]:,} among {counts[2]:,} with the odd tap smaller. "
                  f"The complete support list contains {len(published)} irreducibles.")
            if args.joint:
                joint_counts(n, args.sector)
