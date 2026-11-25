"""Compare the reciprocal-root sieve with direct polynomial gcd computations."""

import argparse
from math import gcd, lcm

from make_witnesses import gcd as poly_gcd, x_power


def check_sieve(factor_bound, limit):
    period = lcm(*(2**d - 1 for d in range(1, factor_bound + 1)))
    power = 1 << period.bit_length()
    if limit <= power + period:
        return 0, 0
    h = (1 << (power + period)) | (1 << (2 * period)) | 1
    obstruction = (1 << (2 * (power + period))) | (1 << period) | 1
    tested = squarefree = 0
    for n in range(1, limit + 1):
        n_unity = (1 << n) | 1
        for w in range(1, (n - 1) // (power + period) + 1, 2):
            if 2 * power * w <= n or gcd(n, w) != 1:
                continue
            u = period * w
            v = 2 * n - (2 * power + period) * w
            support = (0, u, v, u + v, n)
            f = sum(1 << i for i in support)
            reciprocal = sum(1 << (n - i) for i in support)
            derivative = sum(1 << (i - 1) for i in support if i % 2)
            c = power if n % 2 else power + period
            predicted = poly_gcd(h, x_power(n - c * w, h) ^ 1) == 1
            actual = poly_gcd(f, derivative) == 1
            if not (0 < u < v < u + v < n and gcd(n, u, v) == 1):
                raise ValueError(f"invalid support {support}")
            if actual != predicted or poly_gcd(f, reciprocal) != 1:
                raise ValueError(f"gcd disagreement for {support}")
            if poly_gcd(f, n_unity).bit_length() != poly_gcd(obstruction, n_unity).bit_length():
                raise ValueError(f"roots-of-unity gcd degrees disagree for {support}")
            for d in range(1, factor_bound + 1):
                if poly_gcd(f, x_power(1 << d, f) ^ 2) != 1:
                    raise ValueError(f"small factor for {support} at d={d}")
            tested += 1
            squarefree += actual
    return tested, squarefree


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int, nargs="?", default=256)
    parser.add_argument("--factor-bound", type=int, default=3)
    args = parser.parse_args()
    if min(args.factor_bound, args.limit) < 1:
        parser.error("the factor bound and degree limit must be positive")
    total, squarefree = check_sieve(args.factor_bound, args.limit)
    print(f"Checked {total} supports through degree {args.limit} for B={args.factor_bound}. "
          f"{squarefree} are squarefree.")
