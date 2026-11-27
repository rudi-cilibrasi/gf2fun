"""Test progression supports against products of two maximal binary subfields with odd relative degrees."""

import argparse
import subprocess
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from math import gcd

from sympy import divisors, factorint, n_order, primerange


def bounded_primes(limit):
    by_order = defaultdict(list)
    for ell in primerange(3, limit + 1):
        by_order[int(n_order(2, ell))].append(ell)
    return by_order


def relative_primes(p, s, n, by_order):
    """Primes up to n dividing (2^(sp)-1)/(2^s-1), including the ramified prime p."""
    primes = {ell for d in divisors(s*p) if s % d for ell in by_order.get(d, ()) if ell <= n}
    if pow(2, s, p) == 1:
        primes.add(p)
    return sorted(primes)


def possible_steps(primes, limit):
    return sorted({k for ell in primes for k in range(ell, limit+1, ell)})


def candidate_taps(n, first, second):
    supports = set()
    for step_primes, pair_primes in ((first, second), (second, first)):
        differences = possible_steps(pair_primes, n)
        for d in possible_steps(step_primes, n//2):
            for h in differences:
                if h == n:
                    # Both endpoints lie in the pair. Reverse the progression if necessary.
                    for t in range(1, (n-2*d)//2+1):
                        if gcd(gcd(t, d), n) == 1:
                            supports.add((t, t+d, t+2*d))
                    continue
                # One endpoint is in the progression. Reflect it to start at zero.
                a = n-h
                if a == d or a == 2*d or gcd(gcd(d, a), n) != 1:
                    continue
                taps = tuple(sorted((d, 2*d, a)))
                supports.add(min(taps, tuple(n-k for k in reversed(taps))))
    return sorted(supports)


def check_row(row, checker):
    n, p, q, first, second = row
    taps = candidate_taps(n, first, second)
    if not taps:
        return 0, 0, 0
    lines = [f"{n} {p} {q} {len(taps)}", *(" ".join(map(str, t)) for t in taps)]
    result = subprocess.run([checker], input="\n".join(lines)+"\n", text=True,
                            stdout=subprocess.PIPE, check=True)
    count, irreducible, split = map(int, result.stdout.split())
    if count != len(taps) or not 0 <= split <= irreducible <= count:
        raise ArithmeticError(f"invalid census for degree {n}")
    return count, irreducible, split


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    bounds = parser.add_mutually_exclusive_group()
    bounds.add_argument("--limit", type=int, default=100000)
    bounds.add_argument("--degree", type=int, help="check one odd degree with two distinct prime factors")
    parser.add_argument("--checker", help="compiled scripts/relative_progression_orders.cpp for exact testing")
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    limit = args.degree if args.degree is not None else args.limit
    if limit < 3 or args.jobs < 1:
        parser.error("expected a positive worker count and a degree bound of at least three")
    by_order = bounded_primes(limit)
    degrees = [args.degree] if args.degree is not None else range(3, limit+1, 2)
    total = 0
    rows = []
    for n in degrees:
        fs = factorint(n)
        if n % 2 == 0 or len(fs) != 2 or (args.degree is None and max(fs.values()) == 1):
            if args.degree is not None:
                parser.error("expected an odd degree with two distinct prime factors")
            continue
        total += 1
        p, q = sorted(fs)
        s = n//(p*q)
        first, second = (relative_primes(j, s, n, by_order) for j in (p, q))
        if args.degree is not None:
            print(f"Degree {n}, relative primes up to {n}: {p} -> {first}, {q} -> {second}.")
        if first and second and 2*min(first[0], second[0]) < n:
            rows.append((n, p, q, first, second))
    print(f"The two differences exclude all normalized supports in {total-len(rows)} of {total} degrees.")
    if args.checker:
        with ThreadPoolExecutor(args.jobs) as pool:
            counts = list(pool.map(lambda row: check_row(row, args.checker), rows))
        candidates, irreducible, split = map(sum, zip((0, 0, 0), *counts))
        print(f"{candidates} reciprocal representatives, {irreducible} irreducible, {split} split.")


if __name__ == "__main__":
    main()
