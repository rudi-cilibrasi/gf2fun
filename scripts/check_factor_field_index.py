"""Check the uniform index bound for the factor bases from two adjacent even degrees."""

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


def multipliers(n):
    return [k for k in range(1, 21) if (2*k*n+1) % 8 in (1, 7) and gcd(2*k*n+1, 15) == 1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="list small prime-index tests for a prime degree")
    args = parser.parse_args()
    uniform_bound()
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
