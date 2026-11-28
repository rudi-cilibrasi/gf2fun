"""Decode sparse prime-index failures and verify their sharp code lengths for 0 <= h/n <= 300."""

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, groupby

from flint import fmpz

from check_cubed_parity import X, polynomial
from check_linear_order_classes import reflection
from check_sparse_circuit_orders import binary_degree
from check_sparse_root_orders import cyclotomic_census


def index_groups(n, limit):
    # For n >= 23, the small prime-index subgroup theorem excludes every failure.
    if not 2 <= n <= 22:
        return {}
    order = (1 << n)-1
    return {int(p): order//int(p) for p, _ in fmpz(order).factor() if order//int(p) <= limit*n}


def failures(n, groups):
    found = {}
    if groups:
        for taps in combinations(range(1, n), 3):
            if taps > reflection(n, taps):
                continue
            f = polynomial((0, *taps, n))
            if f.is_irreducible():
                primes = tuple(sorted(p for p, h in groups.items() if X.pow_mod(h, f) == 1))
                if primes:
                    found[taps] = primes
    return found


def verify_by_order(groups, found, ntl):
    cases = {(n, r) for n, sizes in groups.items() for h in sizes.values()
             for r in range(3, h+1, 2) if h % r == 0 and binary_degree(r) == n}
    counts = Counter()
    for (n, r), (_, oriented) in cyclotomic_census(sorted(cases), ntl).items():
        self_reciprocal = n % 2 == 0 and pow(2, n//2, r) == r-1
        pairs, rem = divmod(oriented, 1 if self_reciprocal else 2)
        if rem:
            raise ArithmeticError(f"unpaired factors in degree {n} at order {r}")
        primes = tuple(sorted(p for p, h in groups[n].items() if h % r == 0))
        counts[n, primes] += pairs
    if counts != Counter((n, primes) for n, rows in found.items() for primes in rows.values()):
        raise ArithmeticError("the support census and exact-order census disagree")


def check_capacity(ntl):
    groups = {n: index_groups(n, 300) for n in range(2, 23)}
    found = {n: failures(n, sizes) for n, sizes in groups.items()}
    if ntl:
        verify_by_order(groups, found, ntl)
    events = sorted((Fraction(h, n), n, p) for n, sizes in groups.items() for p, h in sizes.items())
    unions = defaultdict(set)
    fixed = total = 0
    changes = []
    for ratio, equal_events in groupby(events, key=lambda event: event[0]):
        old = fixed, total
        for _, n, p in equal_events:
            members = {t for t, primes in found[n].items() if p in primes}
            unions[n].update(members)
            fixed = max(fixed, len(members))
            total = max(total, len(unions[n]))
        if (fixed, total) != old:
            changes.append((str(ratio), fixed, total))
    expected = [('5/4', 1, 1), ('33/10', 2, 2), ('73/9', 3, 3), ('93/10', 3, 4),
                ('341/10', 6, 10), ('273/4', 6, 11), ('455/4', 10, 18)]
    if changes != expected:
        raise ArithmeticError(f"unexpected capacity changes: {changes}")
    for ratio, fixed, total in changes:
        print(f"At h/n = {ratio} the maxima are {fixed} for one prime and {total} across primes.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="list the failing reciprocal representatives in this degree")
    parser.add_argument("--prime", type=int, help="select a single failing prime in the requested degree")
    parser.add_argument("--limit", type=Fraction, default=Fraction(300), help="upper bound on h/n, inclusive")
    parser.add_argument("--ntl", metavar="CENSUS", help="independently check each exact order using NTL")
    args = parser.parse_args()
    if not 0 <= args.limit <= 300 or (args.degree is not None and args.degree < 1):
        parser.error("select a positive degree and a ratio between zero and 300")
    if args.prime is not None and not fmpz(args.prime).is_prime():
        parser.error("--prime requires a prime integer")
    if args.degree is None:
        if args.prime is not None or args.limit != 300:
            parser.error("--prime and --limit select representatives with --degree")
        check_capacity(args.ntl)
    else:
        if args.ntl:
            parser.error("--ntl replays the complete census")
        found = failures(args.degree, index_groups(args.degree, args.limit))
        selected = [(t, ps) for t, ps in sorted(found.items()) if args.prime is None or args.prime in ps]
        print(f"{len(selected)} reciprocal classes.")
        for index, (taps, primes) in enumerate(selected):
            print(f"Index {index} has taps {taps} and failing primes {primes}.")
