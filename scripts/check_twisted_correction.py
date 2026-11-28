"""Bound primes in the cyclotomic norm correction for C_141 and C_191."""

import argparse
import json
from concurrent.futures import ProcessPoolExecutor
from functools import partial
from math import prod
from pathlib import Path

from flint import fmpz


DATA = Path(__file__).resolve().parents[1] / "data" / "translation-lift-orders.json"
# Each entry is checked by one modular exponentiation.
LOG_THREE = {
    141: 1189854635141435548764595604064217390090166,
    191: 2102673075293559018416977571517569060043734472716212973710,
}


def relation_basis(d, j):
    """Gauss-reduce a basis for u + j*v = 0 mod d."""
    a, b = (d, 0), (-j % d, 1)
    while True:
        aa = a[0] ** 2 + a[1] ** 2
        bb = b[0] ** 2 + b[1] ** 2
        if aa > bb:
            a, b = b, a
            aa = bb
        dot = a[0] * b[0] + a[1] * b[1]
        if 2 * abs(dot) <= aa:
            return a, b
        multiple = (2 * dot + aa) // (2 * aa)
        b = (b[0] - multiple * a[0], b[1] - multiple * a[1])


def binomial(u, v):
    positive = fmpz(3) ** max(v, 0) << max(u, 0)
    negative = fmpz(3) ** max(-v, 0) << max(-u, 0)
    return abs(positive - negative)


def correction(d, j):
    """Compute gcd(2^d - 1, 2^(j mod d) - 3) using short relations."""
    a, b = relation_basis(d, j)
    if (abs(a[0] * b[1] - a[1] * b[0]) != d
            or any((u + j * v) % d for u, v in (a, b))):
        raise ValueError(f"invalid relation basis at d={d}")
    h = binomial(*a)
    if h == 1:
        return 1
    # For a very long second vector, test the original two relations modulo h.
    if max(map(abs, b)) > 8 * max(map(abs, a)):
        h = h.gcd(pow(fmpz(2), d, h) - 1)
        return int(h.gcd(pow(fmpz(2), j % d, h) - 3))
    return int(h.gcd(binomial(*b)))


def check(k, factors, jobs):
    j = LOG_THREE[k]
    p = (1 << k) + 5
    if prod(factors) != p - 1 or any(not fmpz(q).is_prime() for q in set(factors)):
        raise ValueError(f"incomplete factorization of p-1 at k={k}")
    if (not fmpz(p).is_prime() or any(pow(-2, (p - 1) // q, p) == 1 for q in set(factors))
            or pow(2, j, p) != 3):
        raise ValueError(f"invalid prime, order or discrete logarithm at k={k}")
    half_factors = list(factors)
    half_factors.remove(2)
    limit = max(half_factors) - 1 if k == 141 else 10**16
    divisors = {1}
    for q in half_factors:
        divisors |= {d * q for d in divisors if d * q <= limit}
    # If d divides e, the correction at d divides the one at e.
    primes = set(half_factors)
    maximal = sorted(d for d in divisors if all(d * q not in divisors for q in primes))
    with ProcessPoolExecutor(jobs) as pool:
        for d, value in zip(maximal, pool.map(partial(correction, j=j), maximal)):
            if value != 1:
                raise ValueError(f"nontrivial correction at k={k}, d={d}: {value}")
    print(f"C_{k}: gcd 1 for {len(maximal)} maximal divisors, covering "
          f"all {len(divisors)} divisors of (p-1)/2 up to {limit}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("jobs must be positive")
    inputs = json.loads(DATA.read_text())["torus_prime_minus_one"]
    for exponent in LOG_THREE:
        check(exponent, inputs[str(exponent)], args.jobs)
