"""Verify the uniform generation and index bounds for low-degree polynomial values."""

import argparse
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


def multipliers(n):
    return [k for k in range(1, 21) if (2*k*n+1) % 8 in (1, 7) and gcd(2*k*n+1, 15) == 1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="list small prime-index tests for a prime degree")
    args = parser.parse_args()
    uniform_bound()
    interval_bounds()
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
