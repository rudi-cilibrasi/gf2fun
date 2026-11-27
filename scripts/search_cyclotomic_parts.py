"""Find fully trial-factored or probable-prime cyclotomic remainders of binary field orders."""

import argparse
import csv
import sys
from concurrent.futures import ProcessPoolExecutor
from itertools import chain
from math import isqrt, lcm

from flint import fmpz


def prime_mask(bound):
    mask = bytearray([1]) * (bound+1)
    mask[:2] = bytes(2)
    for p in range(2, isqrt(bound)+1):
        if mask[p]:
            mask[p*p::p] = bytes((bound-p*p)//p+1)
    return mask


def initialize(bound):
    global trial_primes
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    trial_primes = prime_mask(bound)


def search(n):
    degree_primes = [int(p) for p, _ in fmpz(n).factor()]
    lower = [n//p for p in degree_primes]
    part = ((1 << n)-1) // lcm(*((1 << d)-1 for d in lower))
    bound = len(trial_primes)-1
    small = []
    # A prime of Phi_n(2) either divides n or has multiplicative degree n.
    for p in chain(degree_primes, range(n+1, bound+1, n)):
        if p <= bound and trial_primes[p]:
            while part % p == 0:
                small.append(p)
                part //= p
    if part > 1 and not fmpz(part).is_probable_prime():
        return None
    return (n, " ".join(map(str, sorted(lower))), " ".join(map(str, sorted(small))),
            len(str(part)), "fully factored" if part == 1 else "probable prime")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--end", type=int, required=True)
    parser.add_argument("--trial-limit", type=int, default=2000000)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if not 2 <= args.start <= args.end or args.trial_limit < 2 or args.jobs < 1:
        parser.error("expected a degree interval starting at two, a trial bound of at least two and positive jobs")
    degrees = range(args.start, args.end+1)
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(("degree", "maximal_subfield_degrees", "trial_factors", "remainder_digits", "remainder_status"))
    if args.jobs == 1:
        initialize(args.trial_limit)
        writer.writerows(row for row in map(search, degrees) if row is not None)
    else:
        with ProcessPoolExecutor(args.jobs, initializer=initialize, initargs=(args.trial_limit,)) as pool:
            writer.writerows(row for row in pool.map(search, degrees) if row is not None)


if __name__ == "__main__":
    main()
