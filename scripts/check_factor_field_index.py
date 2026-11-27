"""Verify the uniform generation and index bounds for low-degree polynomial values."""

import argparse
from collections import defaultdict
from fractions import Fraction
from math import gcd

from check_factor_base import irreducible_counts, moment_bound


OUTER = (0, 0, 0, 38, 77, 91, 71, 34, 9, 2)
MIDDLE = (1, 5, 29, 82, 124, 124, 82, 29, 5, 1)
BLOCKS = (OUTER, MIDDLE, OUTER[::-1])


def at(block, value):
    return sum(c * value**i for i, c in enumerate(block))


def uniform_bound():
    norm = sum(c*c for block in BLOCKS for c in block)
    adjacent = list(zip(BLOCKS, BLOCKS[1:]))
    lag_minus = sum(a[i]*b[i-1] for a, b in adjacent for i in range(1, len(a)))
    lag_full = sum(a[i]*b[i] for a, b in adjacent for i in range(len(a)))
    surplus = 2*(lag_minus + 2*lag_full) - 4*norm
    if (norm, lag_minus, lag_full, surplus) != (89806, 61126, 61606, 9452):
        raise ArithmeticError("incorrect norm or autocorrelations")

    # For y=2^d, the product C(2) C(1/2) / y^2 decreases as y increases.
    y = 2**11
    high = sum(Fraction(at(block, 2), y**(2-j)) for j, block in enumerate(BLOCKS))
    low = sum(at(block, Fraction(1, 2)) / y**j for j, block in enumerate(BLOCKS))
    if 8*high*low >= 83*surplus:
        raise ArithmeticError("the bound at d=11 does not control the tail")

    floors = []
    for d in range(4, 11):
        q = 2**(d-1)
        least_n = 24 if d == 4 else 2**d + 3
        limit = min(4*d+12, least_n-1)
        weights = [0]*(limit+1)
        for j, block in enumerate(BLOCKS):
            for i, value in enumerate(block):
                k = 2*(j*d+i)
                if k <= limit:
                    weights[k] += value
        counts = {e: v for e, v in irreducible_counts(2*d).items()
                  if (2*d-2) % e == 0 or (2*d) % e == 0}
        score = moment_bound(counts, 83*q+1, limit, weights=weights)
        if score <= 4*q:
            raise ArithmeticError(f"insufficient finite score at d={d}")
        floors.append(int(score))
    print(f"Exact moment floors for d=4 through 10: {floors}.")
    print("The decreasing tail bound at d=11 proves the index is at most 83q for every d >= 11.")


# Each row specifies the high-degree interval length, excluded index, the
# guaranteed small degrees, and two lists of weights. Odd-position weights
# are divided by sqrt(2). The second list starts at position 2d.
INTERVALS = (
    (3, 41, 3, (0, 7, 13, 28, 22, 27, 12, 7), (5, 17, 19, 31, 20, 19, 5)),
    (4, 8, 4, (0, 0, 2, 4, 3, 3, 1), (1, 3, 3, 4, 2)),
    (5, 5, 5, (0, 0, 1, 3, 2, 2, 1), (1, 2, 2, 3, 1)),
    (7, 3, 5, (0, 0, 0, 0, 3, 6, 3, 3, 1, 1), (1, 2, 2, 4, 4, 4)),
)


def norm(block):
    return sum(Fraction(v*v, 2**(i%2)) for i, v in enumerate(block))


def weighted_pair(i, u, j, v):
    # Includes 2^((j-i)/2) and the odd-position weight denominators.
    return u*v * Fraction(2)**((j-i-i%2-j%2)//2)


def interval_bounds():
    for width, index, small, left, right in INTERVALS:
        bad = Fraction(-1, index-1)
        good = Fraction(197, 200) if width == 7 else 1
        denom = norm(left) + norm(right)
        cross = sum(weighted_pair(i, u, j, v) * (good if 1-width <= j-i <= 0 else bad)
                    for i, u in enumerate(left) for j, v in enumerate(right))
        within = sum(weighted_pair(i, u, j, v) * (1 if j-i <= small else bad)
                     for block in (left, right) for i, u in enumerate(block)
                     for j, v in enumerate(block) if i < j)
        leading, constant = 4*cross/denom, 2*within/denom
        if leading <= 4 or constant < 0:
            raise ArithmeticError(f"insufficient bound for {width} consecutive fields")
        print(f"{width} fields: score at least ({leading})q + {constant}, excluding index >= {index}.")
        if width == 7:
            # The supports overlap only at d=4. Work directly with their sum.
            combined = list(left) + [0]*(8+len(right)-len(left))
            for j, v in enumerate(right):
                combined[8+j] += v
            score = 2*sum(weighted_pair(i, u, j, v) *
                          (1 if j-i <= small else good if j-i <= 8 else bad)
                          for i, u in enumerate(combined) for j, v in enumerate(combined) if i < j)
            score /= norm(combined)
            if score != Fraction(83008, 2125) or score <= 32:
                raise ArithmeticError("d=4 does not pass the seven-field bound")
            print(f"The overlapping d=4 case gives {score} > 32.")


SIX_LEFT = (58, 120, 59, 56, 24, 17, 1, -5, -1, 2)
SIX_RIGHT = (1, -2, -4, 1, 12, 34, 39, 83, 85, 82)
SIX_FINITE = {
    9: (29, 60, 29, 28, 12, 8, 0, -2, 0, 3, 2, 0, -2, 1, 6, 17, 20, 42, 42, 41),
    10: (31, 63, 31, 29, 13, 9, 0, -3, -1, 1, 1, 1, 0, -1, -2, 1, 6, 18, 21, 44, 45, 43),
    11: (28, 58, 28, 27, 12, 8, 1, -3, -1, 1, 1, 0, 0, 1, 0, -1, -2, 1, 6, 16, 19, 40, 41, 40),
}


def weighted_lags(left, right):
    """Return 2^(h/2) times the correlation at h, with signed entries."""
    lags = defaultdict(Fraction)
    for i, u in enumerate(left):
        for j, v in enumerate(right):
            lags[j-i] += weighted_pair(i, u, j, v)
    return lags


def signed_lower(value, lower):
    """Lower bound for value times a number in [lower, 1]."""
    return min(value, value*lower)


def six_field_bounds():
    good, bad = Fraction(3997, 4000), Fraction(-1, 2)
    energy = norm(SIX_LEFT) + norm(SIX_RIGHT)
    cross = weighted_lags(SIX_LEFT, SIX_RIGHT)
    slope = sum(signed_lower(v, good if 3 <= h <= 8 else bad)
                for h, v in cross.items()) / (4*energy)
    a, b = (weighted_lags(s, s) for s in (SIX_LEFT, SIX_RIGHT))
    inside = 2*sum(signed_lower(a[k]+b[k], bad) for k in range(1, 10)) / energy
    if (slope, inside) != (Fraction(2089970613, 522304000), Fraction(-37473, 8161)):
        raise ArithmeticError("incorrect six-field correlations")
    if slope <= 4 or (slope-4)*4096 + inside <= 1:
        raise ArithmeticError("the six-field tail does not reach n-2")

    for d in range(4, 13):
        m = 2*d
        weights = [0]*(m+2)
        for start, packet in ((0, SIX_LEFT), (m-8, SIX_RIGHT)):
            for i, value in enumerate(packet):
                weights[start+i] += value
        weights = SIX_FINITE.get(d, weights)
        lags = weighted_lags(weights, weights)
        for p in (3, 5):
            total = 0
            for k in range(1, len(weights)):
                size = 2**k
                # Every omitted element of a subfield is omitted in its containing field.
                covered = max([0] + [size-2**j//2000 for j in range(m-5, m+1) if j % k == 0])
                if p == 3 and k % 3 == 0:
                    covered = max(covered, 2**(k//3))
                lower = Fraction(p*covered-size, (p-1)*size)
                total += lags[k]/size + signed_lower(lags[k], lower)
            if 2*total <= 2**(d+1)*norm(weights):
                raise ArithmeticError(f"insufficient signed moment at d={d}, prime class {p}")
    print("Six fields with at least 1999/2000 coverage each generate the full group in every degree n >= 24.")


def multipliers(n):
    return [k for k in range(1, 21) if (2*k*n+1) % 8 in (1, 7) and gcd(2*k*n+1, 15) == 1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="list small prime-index tests for a prime degree")
    args = parser.parse_args()
    uniform_bound()
    interval_bounds()
    six_field_bounds()
    residues = [a for a in range(60) if gcd(a, 60) == 1]
    maximum = max(len(multipliers(a)) for a in residues)
    if maximum != 6:
        raise ArithmeticError("unexpected prime-degree sieve")
    print("At most six candidates survive modulo 3, 5 and 8 in every prime degree n >= 29.")
    # With three further small primes, six unit classes have no possible divisor.
    empty = [a for a in range(60060) if gcd(a, 60060) == 1
             and all(gcd(2*k*a+1, 7*11*13) > 1 for k in multipliers(a))]
    if empty != [1523, 11741, 19231, 34939, 44819, 49591]:
        raise ArithmeticError("unexpected sieve classes modulo 60060")
    print(f"No power tests are needed for primes in the classes {empty} modulo 60060.")
    if args.degree is not None:
        from flint import fmpz
        n = args.degree
        if n < 29 or not fmpz(n).is_prime():
            parser.error("--degree requires a prime at least 29")
        d = (n-3).bit_length()-1
        q = 2**(d-1)
        candidates = [2*k*n+1 for k in multipliers(n) if 2*k*n+1 <= 83*q]
        primes = [p for p in candidates if fmpz(p).is_prime() and pow(2, n, p) == 1]
        print(f"Degree {n}, d={d}, 83q={83*q}. Prime divisors requiring a power test: {primes}.")


if __name__ == "__main__":
    main()
