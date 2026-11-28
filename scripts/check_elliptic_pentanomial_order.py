#!/usr/bin/env python3
"""Count the Eisenstein endomorphisms in the elliptic pentanomial order bound."""

from functools import cache
from math import comb, gcd, isqrt, prod


def sum_squares(n):
    return n * (n + 1) * (2 * n + 1) // 6


def residue_moments(limit, first):
    """Count, sum, and square sum of first, first+3, ... through limit."""
    count = (limit + 3 - first) // 3
    steps = count * (count - 1) // 2
    return (
        count,
        first * count + 3 * steps,
        first**2 * count + 6 * first * steps + 9 * sum_squares(count - 1),
    )


def unrestricted_pairs(limit):
    """Pairs 1 <= b < a <= limit with 3 not dividing a+b, before the gcd test."""
    moments = [residue_moments(limit, first) for first in (3, 1, 2)]
    count = weight = 0
    for r, (cr, sr, tr) in enumerate(moments):
        for s, (cs, ss, ts) in enumerate(moments):
            if (r + s) % 3:
                count += cr * cs
                weight += tr * cs - sr * ss + cr * ts
        if r:
            count -= cr
            weight -= tr
    return count // 2, weight // 2


@cache
def coprime_pairs(limit):
    """Remove all pairs with gcd > 1, grouping divisors by floor(limit/d)."""
    count, weight = unrestricted_pairs(limit)
    lo = 2
    while lo <= limit:
        quotient = limit // lo
        hi = limit // quotient
        first = lo - 1
        multiples = hi // 3 - first // 3
        copies = hi - first - multiples
        squares = sum_squares(hi) - sum_squares(first)
        squares -= 9 * (sum_squares(hi // 3) - sum_squares(first // 3))
        smaller_count, smaller_weight = coprime_pairs(quotient)
        count -= copies * smaller_count
        weight -= squares * smaller_weight
        lo = hi + 1
    return count, weight


def direct_pairs(limit):
    norms = [
        a * a - a * b + b * b
        for a in range(1, limit + 1)
        for b in range(1, a)
        if (a + b) % 3 and gcd(a, b) == 1
    ]
    return len(norms), sum(norms)


# At stage i use at most m linear factors for every pair with a <= limit.
STAGES = (
    (1, 2445312), (2, 2020352), (4, 1691648), (8, 1347584),
    (16, 1029120), (32, 760832), (64, 551936), (128, 395264), (256, 281600),
)


def check_integer_order(degree):
    factors = (2, 3, 499, 1163, 2657, 155377, 13455809771)
    for prime in factors:
        assert all(prime % d for d in range(2, isqrt(prime) + 1))
    assert prod(factors) == degree
    modulus = degree + 1
    assert pow(2, degree, modulus) == 1
    assert all(pow(2, degree // prime, modulus) != 1 for prime in factors)
    # Lucas's criterion gives both primality and exact order.
    return gcd(degree, pow(2, degree, degree) - 1)


def main():
    for limit in range(101):
        assert direct_pairs(limit) == coprime_pairs(limit)
    degree = 2**84 + 2
    index = check_integer_order(degree)
    assert index == 3
    counts = [coprime_pairs(limit) for _, limit in STAGES] + [(0, 0)]
    budget = 0
    scaled_bits = 0
    scale = 16384
    print("max_a multiplicity new_pairs sum_of_norms")
    for i, (multiplicity, limit) in enumerate(STAGES):
        count = counts[i][0] - counts[i + 1][0]
        weight = counts[i][1] - counts[i + 1][1]
        choices = comb(multiplicity + 4, 4)
        log_floor = (choices**scale).bit_length() - 1
        budget += multiplicity * weight
        scaled_bits += count * log_floor
        print(limit, multiplicity, count, weight)
    assert 2 * budget < degree
    certified_bits = scaled_bits // scale - (index - 1).bit_length()
    assert certified_bits > 9_000_000_000_000
    print(f"common numerator degree <= {budget} < {degree // 2}")
    print(f"root order >= 2^{certified_bits}, including the index-{index} allowance")


if __name__ == "__main__":
    main()
