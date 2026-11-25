"""Verify a bounded list of odd taps passing four necessary tests in every odd degree from nine."""

import argparse
from functools import cache
from math import gcd, lcm, prod

from flint import fmpz, nmod_poly

from check_odd_tap_parity import factor_parity


X = nmod_poly([0, 1], 2)
PERIOD = 1_249_920
CUTOFF = 6
TAPS = (
    (35, 45), (21, 27), (7, 63), (1, 9), (9, 63), (1, 7), (21, 49), (3, 7),
    (21, 41), (35, 37), (31, 33), (21, 43), (15, 49), (17, 45), (9, 21),
    (7, 55), (27, 33), (9, 23), (19, 37), (5, 7), (5, 9), (15, 55), (1, 3),
    (29, 51), (19, 45), (7, 41), (29, 35), (17, 47), (15, 21), (13, 27),
)
SHORT_EXCEPTIONS = {15: (1, 13), 25: (1, 5)}


@cache
def repeat(period):
    """A one in each position congruent to zero modulo period."""
    if PERIOD % period:
        raise ValueError(f"{period} does not divide the covering period")
    return ((1 << PERIOD)-1) // ((1 << period)-1)


def root_order(f):
    order = 2**f.degree()-1
    factors = fmpz(order).factor()
    if prod(int(p)**e for p, e in factors) != order or not all(p.is_prime() for p, _ in factors):
        raise ArithmeticError("incomplete factorization of a field order")
    for p, _ in factors:
        p = int(p)
        while order % p == 0 and X.pow_mod(order//p, f) == 1:
            order //= p
    return order


def small_fields():
    sieve = X**0
    for k in range(1, CUTOFF+1):
        field = X**(2**k-1)+1
        sieve = (sieve//sieve.gcd(field))*field
    fields = []
    for f, _ in sieve.factor()[1]:
        powers = []
        logs = {}
        power = X**0
        while tuple(power.coeffs()) not in logs:
            logs[tuple(power.coeffs())] = len(powers)
            powers.append(power)
            power = (power*X) % f
        fields.append((f, powers, logs))
    return fields


def direct(n, u, v):
    if not (0 < u < v < u+v < n) or gcd(n, gcd(u, v)) != 1:
        return False
    f = X**n + (1+X**u)*(1+X**v)
    factors = f.factor()[1]
    return (len(factors) % 2 == 1 and all(m == 1 and p.degree() > CUTOFF for p, m in factors)
            and f.gcd(f.reverse()) == 1)


def certified_classes(u, v, fields, audit):
    h = (u+v)//2
    period = lcm(8, 4*h)
    accepted = 0
    for r in range(1, period, 2):
        n = period+r
        predicted = factor_parity(n, u, v)
        if audit:
            f = X**n + (1+X**u)*(1+X**v)
            factors = f.factor()[1]
            actual = None if any(m != 1 for _, m in factors) else len(factors) % 2
            if actual != predicted:
                raise ArithmeticError(f"factor parity disagrees at {(n, u, v)}")
        if predicted and gcd(n, gcd(u, v)) == 1:
            accepted |= 1 << r
    accepted *= repeat(period)

    # At an inverse pair x^(n-h) = 1, so the product polynomial restricts to this fixed polynomial.
    circle = X**(2*h) + X**v + X**h + X**u + 1
    for f, _ in circle.factor()[1]:
        divisor = gcd(root_order(f), PERIOD)
        accepted &= ~(repeat(divisor) << (h % divisor))

    for f, powers, logs in fields:
        order = len(powers)
        value = ((1+powers[u % order])*(1+powers[v % order])) % f
        exponent = logs.get(tuple(value.coeffs()))
        if exponent is not None:
            accepted &= ~(repeat(order) << exponent)
    return accepted


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", action="store_true", help="factor every representative used for parity")
    parser.add_argument("--degree", type=int, help="list tap pairs certified at a specified odd degree")
    args = parser.parse_args()
    if args.degree is not None and (args.degree < 9 or args.degree % 2 == 0):
        parser.error("expected an odd degree of at least nine")
    fields = small_fields()
    classes = {(u, v): certified_classes(u, v, fields, args.audit) for u, v in TAPS}
    covered = 0
    for mask in classes.values():
        covered |= mask
    if covered != 2*repeat(2):
        raise ArithmeticError("the selected taps leave an odd residue uncovered")
    short = {}
    for n in range(9, 81, 2):
        options = [SHORT_EXCEPTIONS[n]] if n in SHORT_EXCEPTIONS else TAPS
        short[n] = [(u, v) for u, v in options if direct(n, u, v)]
        if not short[n]:
            raise ArithmeticError(f"small degree {n} is uncovered")
    print(f"{len(classes)} tap pairs cover all {covered.bit_count():,} odd residues modulo {PERIOD:,}. "
          f"Direct factorizations cover all {len(short)} odd degrees from 9 through 79.")
    if args.degree is not None:
        n = args.degree
        choices = short[n] if n in short else [pair for pair, mask in classes.items() if (mask >> (n % PERIOD)) & 1]
        for u, v in choices:
            print(f"{n},{u},{v}")


if __name__ == "__main__":
    main()
