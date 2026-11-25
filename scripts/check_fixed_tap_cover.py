"""Verify bounded product taps passing the factor and reciprocal tests in every degree from seven."""

import argparse
from functools import cache
from math import gcd, lcm, prod

from flint import fmpz, nmod_poly

from check_odd_tap_parity import factor_parity


X = nmod_poly([0, 1], 2)
PERIOD = 1_249_920
CUTOFF = 6
ODD_TAPS = (
    (35, 45), (21, 27), (7, 63), (1, 9), (9, 63), (1, 7), (21, 49), (3, 7),
    (21, 41), (35, 37), (31, 33), (21, 43), (15, 49), (17, 45), (9, 21),
    (7, 55), (27, 33), (9, 23), (19, 37), (5, 7), (5, 9), (15, 55), (1, 3),
    (29, 51), (19, 45), (7, 41), (29, 35), (17, 47), (15, 21), (13, 27),
)
EVEN_TAPS = (
    (15, 63), (7, 27), (35, 45), (33, 35), (21, 49), (13, 31), (31, 45), (3, 75),
    (1, 7), (21, 41), (21, 27), (13, 15), (5, 29), (13, 37), (31, 43), (31, 33),
    (5, 35), (15, 21), (29, 35), (3, 35), (11, 47), (15, 51), (9, 29), (5, 7),
)
SHORT_TAPS = ((1, 13), (1, 5), (5, 21))


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


def factored_parity(n, u, v):
    factors = (X**n + (1+X**u)*(1+X**v)).factor()[1]
    return None if any(m != 1 for _, m in factors) else len(factors) % 2


def certified_classes(u, v, odd, fields, audit):
    h = (u+v)//2
    period = lcm(8, 4*h) if odd else 4*(v-u)
    threshold = 2*h if odd else 3*u+v
    base = period*(threshold//period+1)
    accepted = 0
    for r in range(int(odd), period, 2):
        n = base+r
        predicted = factor_parity(n, u, v) if odd else factored_parity(n, u, v)
        if audit and factored_parity(n+period, u, v) != predicted:
            raise ArithmeticError(f"factor parity disagrees one period later at {(n, u, v)}")
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
    parser.add_argument("--audit", action="store_true", help="verify all parity representatives one period later")
    parser.add_argument("--degree", type=int, help="list tap pairs certified at a specified degree")
    args = parser.parse_args()
    if args.degree is not None and args.degree < 7:
        parser.error("expected a degree of at least seven")
    fields = small_fields()
    classes = {}
    for odd, taps in ((True, ODD_TAPS), (False, EVEN_TAPS)):
        covered = 0
        for u, v in taps:
            mask = certified_classes(u, v, odd, fields, args.audit)
            classes[u, v] = classes.get((u, v), 0) | mask
            covered |= mask
        if covered != repeat(2) << int(odd):
            raise ArithmeticError("the selected taps leave a degree class uncovered")
        kind = "odd" if odd else "even"
        print(f"{len(taps)} tap pairs cover all {covered.bit_count():,} {kind} residues modulo {PERIOD:,}.")
    threshold = max(3*u+v for u, v in EVEN_TAPS)
    short = {7: [(1, 2)]}
    if not direct(7, 1, 2):
        raise ArithmeticError("degree-seven factorization disagrees")
    for n in range(8, threshold+1):
        short[n] = [(u, v) for u, v in (*classes, *SHORT_TAPS) if direct(n, u, v)]
        if not short[n]:
            raise ArithmeticError(f"small degree {n} is uncovered")
    print(f"Direct factorizations cover degrees 7 through {threshold}.")
    if args.degree is not None:
        n = args.degree
        choices = short[n] if n in short else [pair for pair, mask in classes.items() if (mask >> (n % PERIOD)) & 1]
        for u, v in choices:
            print(f"{n},{u},{v}")


if __name__ == "__main__":
    main()
