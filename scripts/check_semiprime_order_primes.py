"""Check the exact full-degree-prime exceptions among odd squarefree semiprime degrees through 10^8."""

import argparse
import csv
from array import array
from bisect import bisect_right
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from math import isqrt
from pathlib import Path

from check_cubed_parity import X, polynomial


DATA = Path(__file__).resolve().parents[1] / 'data' / 'semiprime-full-degree-prime-exceptions.csv'
LIMIT = 100_000_000


def count_degrees(limit):
    bound = limit//3
    prime = bytearray([1]) * (bound+1)
    prime[:2] = bytes(2)
    for p in range(2, isqrt(bound)+1):
        if prime[p]:
            prime[p*p::p] = bytes((bound-p*p)//p+1)
    odd_primes = array('I', (p for p in range(3, bound+1, 2) if prime[p]))
    total = 0
    exceptions = set()
    for i, p in enumerate(odd_primes):
        if p*p > limit:
            break
        total += bisect_right(odd_primes, limit//p) - i - 1
        # For prime p, every divisor prime of 2^p-1 has binary degree p and equals 1 modulo 2p.
        last = min(limit//p, 2**p-1)
        for q in range(2*p+1, last+1, 2*p):
            if prime[q] and pow(2, p, q) == 1:
                exceptions.add((p, q))
    return total, exceptions


def verify_base(entry):
    (p, taps), qs = entry
    f = polynomial((0, *taps, p))
    if not f.is_irreducible():
        raise ArithmeticError(f"reducible base in degree {p}")
    for q in qs:
        if X.pow_mod((2**p-1)//q, f) == 1:
            raise ArithmeticError(f"the base root misses the full {q}-part in degree {p}")


def verify(limit, jobs):
    total, expected = count_degrees(limit)
    bases = defaultdict(list)
    found = set()
    with DATA.open(newline='') as stream:
        for row in csv.DictReader(stream):
            p, q = int(row['p']), int(row['q'])
            if p*q > limit:
                continue
            taps = tuple(map(int, row['base_taps'].split()))
            if (len(taps) not in (1, 3) or tuple(sorted(set(taps))) != taps
                    or taps[0] <= 0 or taps[-1] >= p or (p, q) in found):
                raise ArithmeticError(f"invalid sparse witness at {(p, q)}")
            found.add((p, q))
            bases[p, taps].append(q)
    if found != expected:
        raise ArithmeticError("the archived witnesses differ from the arithmetic exception set")
    with ProcessPoolExecutor(jobs) as pool:
        list(pool.map(verify_base, bases.items()))
    if limit == LIMIT and (total, len(found), len(bases)) != (14424896, 221, 187):
        raise ArithmeticError("incorrect full census totals")
    print(f"Through {limit:,}: {total:,} odd squarefree semiprime degrees. "
          f"A full-degree prime is forced in {total-len(found):,}; "
          f"{len(found)} exceptional degrees have verified dilations from {len(bases)} sparse bases.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--through', type=int, default=LIMIT, help='upper degree, at most 100000000')
    parser.add_argument('--jobs', type=int, default=1, help='number of simultaneous polynomial checks')
    args = parser.parse_args()
    if not 9 <= args.through <= LIMIT or args.jobs < 1:
        parser.error('use an upper degree between 9 and 100000000 and a positive job count')
    verify(args.through, args.jobs)
