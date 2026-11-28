"""Verify the order-prime graph census and all exceptional degrees through 70,000."""

import argparse
import csv
import subprocess
from array import array
from collections import Counter, defaultdict
from concurrent.futures import ProcessPoolExecutor
from math import gcd, isqrt, prod
from pathlib import Path


LIMIT = 1_000_000
WITNESS_LIMIT = 70_000
DATA = Path(__file__).resolve().parents[1] / 'data' / 'squarefree-order-prime-exceptions.csv'


def squarefree_degrees(limit):
    least = array('I', range(limit+1))
    for p in range(3, isqrt(limit)+1, 2):
        if least[p] == p:
            for j in range(p*p, limit+1, 2*p):
                if least[j] == j:
                    least[j] = p
    for n in range(3, limit+1, 2):
        factors = []
        m = n
        while m > 1:
            p = least[m]
            m //= p
            if m % p == 0:
                break
            factors.append(p)
        else:
            if len(factors) >= 2:
                yield n, factors


def count_degrees():
    counts, connected = Counter(), Counter()
    small, exceptions = Counter(), {}
    for n, factors in squarefree_degrees(LIMIT):
        k = len(factors)
        counts[k] += 1
        eligible = {r for r in factors if pow(2, n//r, r) == 1}
        if prod(eligible) != gcd(n, pow(2, n, n)-1):
            raise ArithmeticError(f"incorrect shared order primes at {n}")
        if not eligible:
            connected[k] += 1
        if n <= WITNESS_LIMIT:
            small[k] += 1
            if eligible:
                exceptions[n] = eligible
    if ([counts[k] for k in range(2, 7)] != [168330, 120807, 34334, 3269, 48]
            or [connected[k] for k in range(2, 7)] != [168293, 113833, 25750, 1278, 1]
            or sum(small.values()) != 21436 or len(exceptions) != 1235):
        raise ArithmeticError("incorrect degree census")
    print("Number of primes, odd squarefree degrees, degrees satisfying the coprimality test:")
    for k in sorted(counts):
        print(k, counts[k], connected[k])
    return exceptions


def verify_witnesses(exceptions, ntl, jobs):
    bases = defaultdict(list)
    seen = set()
    with DATA.open(newline='') as stream:
        for row in csv.DictReader(stream):
            n, r = int(row['degree']), int(row['isolated_prime'])
            taps = tuple(map(int, row['base_taps'].split()))
            if n in seen or r not in exceptions.get(n, ()):
                raise ArithmeticError(f"unexpected witness degree or prime at {(n, r)}")
            m = n//r
            if (len(taps) not in (1, 3) or taps != tuple(sorted(set(taps)))
                    or not 0 < taps[0] <= taps[-1] < m):
                raise ArithmeticError(f"invalid base taps at {(n, r)}")
            seen.add(n)
            bases[m, taps].append(r)
    if seen != set(exceptions):
        raise ArithmeticError("the archive does not cover the computed exceptions")
    if ntl:
        work = ''.join(f"{m} {r} {' '.join(map(str, taps))}\n"
                       for (m, taps), primes in bases.items() for r in primes)
        subprocess.run([ntl, '--verify-bases'], input=work, text=True, check=True)
    else:
        from check_semiprime_order_primes import verify_base
        with ProcessPoolExecutor(jobs) as pool:
            list(pool.map(verify_base, bases.items()))
    print(f"Verified {len(seen)} disconnected examples through {WITNESS_LIMIT:,} from {len(bases)} distinct sparse bases.")


def check_example():
    p, r, q = 10007, 10009, 2**61-1
    if any(t % d == 0 for t in (p, r, 61) for d in range(2, isqrt(t)+1)):
        raise ArithmeticError("invalid small prime in the three-prime example")
    a = 4
    for _ in range(61-2):
        a = (a*a-2) % q
    n = p*r*q
    if (a != 0 or gcd(n, pow(2, n, n)-1) != 1 or n <= (p*r+1)**3
            or 2*p*q+1 != 46149141986402870735315):
        raise ArithmeticError("incorrect large-degree example")
    print(f"Degree {n} forces a root-order prime of at least {2*p*q+1}.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ntl', help='compiled check_semiprime_order_exceptions.cpp')
    parser.add_argument('--jobs', type=int, default=1, help='simultaneous FLINT checks')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('jobs must be positive')
    verify_witnesses(count_degrees(), args.ntl, args.jobs)
    check_example()
