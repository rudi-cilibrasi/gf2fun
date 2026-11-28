"""Test progression supports against products of two maximal binary subfields with odd relative degrees."""

import argparse
import subprocess
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from math import gcd, lcm

from sympy import divisors, factorint, isprime, n_order, primerange, totient


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


def positioned_taps(n, d, offset, width, differences):
    # Reflect a triple containing an endpoint to start at zero, leaving n-h and n.
    for h in differences:
        if h == n:
            break
        a = n-h
        if a not in (offset, width) and gcd(gcd(d, a), n) == 1:
            yield tuple(sorted((offset, width, a)))
    # With both endpoints in the pair, reflection also reverses the triple.
    if differences and differences[-1] == n and 2*offset <= width:
        for t in range(1, n-width):
            if gcd(gcd(t, d), n) == 1:
                yield t, t+offset, t+width


def candidate_taps(n, first, second, max_span):
    supports = set()
    for step_primes, pair_primes in ((first, second), (second, first)):
        differences = possible_steps(pair_primes, n)
        for d in possible_steps(step_primes, n//2):
            for span in range(2, min(max_span, (n-1)//d)+1):
                for middle in range(1, span):
                    if gcd(middle, span) == 1:
                        for taps in positioned_taps(n, d, middle*d, span*d, differences):
                            supports.add(min(taps, tuple(n-k for k in reversed(taps))))
    return sorted(supports)


def candidate_batches(rows):
    for n, p, q, first, second, max_span in rows:
        taps = candidate_taps(n, first, second, max_span)
        for start in range(0, len(taps), 2048):
            yield n, p, q, taps[start:start+2048]


def check_batch(batch, checker):
    n, p, q, taps = batch
    lines = [f"{n} {p} {q} {len(taps)}", *(" ".join(map(str, t)) for t in taps)]
    result = subprocess.run([checker], input="\n".join(lines)+"\n", text=True,
                            stdout=subprocess.PIPE, check=True)
    count, irreducible, split = map(int, result.stdout.split())
    if count != len(taps) or not 0 <= split <= irreducible <= count:
        raise ArithmeticError(f"invalid census for degree {n}")
    return count, irreducible, split


def prime_power_family(m, q, b):
    """Eliminate unramified relative primes in degree m*q^b without constructing q^b."""
    coefficients = range(2, m, 2)
    if q > m:
        period = lcm(*(r-1 for r in primerange(3, m+1)))
    else:
        period = lcm(*(int(totient(k*q+1)) for k in coefficients))
    unresolved = []
    for k in coefficients:
        # A prime k*q^b+1 dividing a Mersenne number of odd degree must have 2 as a square.
        if (k*pow(q, b, 8)+1) % 8 in (3, 5):
            continue
        if any(pow(q, b, r) == 1 for r in factorint(k+1)):
            continue
        if b > 1 and pow(q, b-1, k*q+1) == 1:
            continue
        unresolved.append(k)
    return period, unresolved


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    bounds = parser.add_mutually_exclusive_group()
    bounds.add_argument("--limit", type=int, default=100000)
    bounds.add_argument("--degree", type=int, help="check one odd degree with two distinct prime factors")
    bounds.add_argument("--family", type=int, nargs=3, metavar=("M", "Q", "B"),
                        help="test degree M*Q^B for a prime power M using small congruences")
    parser.add_argument("--checker", help="compiled scripts/relative_progression_orders.cpp for exact testing")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--short-triples", action="store_true",
                        help="include all triples in p consecutive equally spaced positions, p the smaller prime")
    args = parser.parse_args()
    if args.family:
        m, q, b = args.family
        fs = factorint(m) if m > 1 else {}
        if len(fs) != 1 or not (2 < min(fs) < q and isprime(q) and b >= 1):
            parser.error("expected M=P^a with odd primes P < Q and a positive exponent B")
        p = min(fs)
        if args.checker:
            parser.error("--checker tests supports at explicit degrees")
        period, unresolved = prime_power_family(m, q, b)
        exponents = f"t*{period}" if q > m else f"1+t*{period}"
        print(f"Degree {m}*{q}^{b}. Exponents {exponents} eliminate all unramified "
              "candidate primes for every t >= 1.")
        if unresolved:
            print(f"Coefficients k requiring a further test for k*{q}^{b}+1: {unresolved}.")
        elif pow(2, m//p, q) == 1:
            print(f"For a support of exponent gcd one, a split requires {q} to divide "
                  "the triple step or the difference of the other two exponents.")
        else:
            print(f"Any irreducible pentanomial with three of {p} equally spaced positions "
                  "has a root outside the product of the maximal subfields.")
        return
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
            rows.append((n, p, q, first, second, p-1 if args.short_triples else 2))
    print(f"The two differences exclude all normalized supports in {total-len(rows)} of {total} degrees.")
    if args.checker:
        with ThreadPoolExecutor(args.jobs) as pool:
            counts = list(pool.map(lambda batch: check_batch(batch, args.checker), candidate_batches(rows)))
        candidates, irreducible, split = map(sum, zip((0, 0, 0), *counts))
        print(f"{candidates} reciprocal representatives, {irreducible} irreducible, {split} split.")


if __name__ == "__main__":
    main()
