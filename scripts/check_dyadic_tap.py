"""Compare binary derivative and finite-field orbit counts with the trinomial order gcd."""

import argparse
from math import gcd

from check_trinomial_triples import pair_and_triple_counts
from make_witnesses import gcd as polynomial_gcd


def derivative_mask(m):
    """Encode (1+X)^m + X^m + 1 as a polynomial over GF(2)."""
    power = 1
    remaining = m
    while remaining:
        term = remaining & -remaining
        power ^= power << term
        remaining -= term
    return power ^ (1 << m) ^ 1


def orbit_counts(j, h):
    d = gcd(j, h)
    fixed_pair = int(d % 2 == 0)
    nonfixed = ((1 << d) - (-1)**d) if (j // d) % 3 == 0 else 0
    return fixed_pair, nonfixed // 3


def check(limit):
    total = 0
    for n in range(2, limit + 1):
        for i in range((n - 1).bit_length()):
            a = 1 << i
            if a >= n or gcd(n, a) != 1:
                continue
            f = (1 << n) | (1 << a) | 1
            pairs, triples = pair_and_triple_counts(n, a)
            common = polynomial_gcd(f, derivative_mask(n - a))
            if common.bit_length() - 1 != 2*pairs + 3*triples:
                raise ArithmeticError(f"derivative disagrees in degree {n} at tap {a}")
            total += 1

    families = 0
    for j in range(1, limit.bit_length()):
        q = 1 << j
        for m, shift, extra_cube_roots in ((q+1, 1, False), (q*q-q+1, 0, False), (q+3, 2, True)):
            for b in range(limit.bit_length()):
                gap = m << b
                if gap >= limit:
                    break
                for i in range((limit - gap).bit_length()):
                    a = 1 << i
                    n = a + gap
                    if n > limit or gcd(a, n) != 1:
                        continue
                    pairs, triples = orbit_counts(j, abs(i-b-shift))
                    if extra_cube_roots:
                        pairs = int((i-b-j) % 2 == 0)
                    if (pairs, triples) != pair_and_triple_counts(n, a):
                        raise ArithmeticError(f"orbit count disagrees for j={j}, m={m}, b={b}, i={i}")
                    families += 1
    print(f"Checked all {total} normalized dyadic taps through degree {limit} and {families} family instances.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int, nargs="?", default=512)
    args = parser.parse_args()
    if args.limit < 2:
        parser.error("the degree limit must be at least two")
    check(args.limit)
