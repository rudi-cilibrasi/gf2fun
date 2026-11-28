"""Check the degree-3073 trinomial candidates, their power images and their known orders."""

import argparse
from math import gcd, prod

from flint import fmpz

from check_factor_base import modulus, polynomial
from check_product_range import prime_index_powers
from check_sparse_root_models import small_factors
from check_trinomial_decimations import short_power_support


Q = 1024
N = 3*Q+1
ORDER = (1 << N)-1
LOWER = ((1 << 7)-1)*((1 << 439)-1)
COFACTOR = ORDER // LOWER
TAPS = (184, 330, 492, 915, 999, 1023, 1269, 1425)
LIMIT = 10**10
X = polynomial(2)


def check_group():
    primes = [127, 104110607, 127321491658223, 122551752733003055543]
    primes.append(LOWER // prod(primes))
    if prod(primes) != LOWER or not all(fmpz(p).is_prime() for p in primes):
        raise ValueError("incorrect maximal-subfield order factors")
    if LOWER*COFACTOR != ORDER or gcd(LOWER, COFACTOR) != 1 or pow(3, COFACTOR-1, COFACTOR) == 1:
        raise ValueError("incorrect composite cofactor")
    # Every prime of C has binary order 3073, as 7 and 439 are the maximal proper divisors.
    if any(COFACTOR % k == 0 for k in range(2*N+1, LIMIT+1, 2*N)):
        raise ValueError("small divisor of the cofactor")
    return primes


def irreducible(f):
    return (X.pow_mod(1 << N, f) == X
            and all((X.pow_mod(1 << d, f) + X).gcd(f) == 1 for d in (7, 439)))


def census():
    small = small_factors()
    taps = []
    for tap in range(1, N//2+1):
        f = modulus(N, (tap,))
        if f.gcd(small) == 1 and irreducible(f):
            taps.append(tap)
    if tuple(taps) != TAPS:
        raise ValueError(f"unexpected irreducible trinomial taps: {taps}")
    print(f"Checked all {N//2} reciprocal classes of trinomials.")


def images(tap, f):
    for power in (3, 5, 7, 9, 17, 33, 65, 129, 257, 513, 1025, 2049):
        support = short_power_support((0, tap, N), power)
        if not support or len(support) != 5:
            continue
        if gcd(power, ORDER) != 1 or sum((X.pow_mod(power*e, f) for e in support), X*0) != 0:
            raise ValueError(f"incorrect equal-order image at tap {tap}, power {power}")
        reciprocal = tuple(N-e for e in reversed(support))
        yield power, min(support, reciprocal)[1:-1]


def check_coordinate(f):
    if gcd(Q+1, ORDER) != 1:
        raise ValueError("the coordinate change must preserve order")
    w = X.pow_mod((Q+1)*pow(2, -1, ORDER) % ORDER, f)
    denominator = (w+1).pow_mod(2, f)
    if (w.pow_mod(2, f) != X.pow_mod(Q+1, f) or w*denominator % f != X
            or X.pow_mod(Q, f)*denominator % f != w):
        raise ValueError("the rational Frobenius identities failed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", action="store_true", help="repeat the exhaustive irreducibility search")
    parser.add_argument("--images", action="store_true", help="list each reciprocal pair of power images")
    args = parser.parse_args()
    primes = check_group()
    if args.census:
        census()
    pairs = set()
    for tap in TAPS:
        f = modulus(N, (tap,))
        if (not irreducible(f) or X.pow_mod(LOWER, f) == 1
                or any(z == 1 for _, z in prime_index_powers(X, ORDER, primes, f))):
            raise ValueError(f"missing order component at tap {tap}")
        if tap == Q-1:
            check_coordinate(f)
        for power, taps in images(tap, f):
            if taps in pairs:
                raise ValueError(f"duplicate image at tap {tap}, power {power}")
            pairs.add(taps)
            if args.images:
                print(f"Trinomial tap {tap}, power {power}, pentanomial taps {taps}.")
    if len(pairs) != 23:
        raise ValueError(f"unexpected number of pentanomial pairs: {len(pairs)}")
    print(f"{len(TAPS)} trinomial pairs and {len(pairs)} pentanomial pairs pass all five known "
          f"prime-index tests. Each remaining index is one or exceeds {LIMIT}.")


if __name__ == "__main__":
    main()
