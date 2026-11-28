"""Bound the densities of degrees admitting no binary primitive or irreducible trinomial."""

import argparse
import csv
from array import array
from fractions import Fraction
from itertools import combinations
from math import gcd, isqrt, lcm, prod
from pathlib import Path


DATA = Path(__file__).resolve().parents[1] / "data"


def prime_factors(n):
    p = 2
    while p * p <= n:
        if n % p == 0:
            yield p
            while n % p == 0:
                n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        yield n


def totient(n):
    result = n
    for p in prime_factors(n):
        result -= result // p
    return result


def field_polynomials():
    moduli = {d: (1 << d) | 3 for d in (2, 3, 4)}
    with (DATA / "product-witnesses-5-1206.csv").open() as source:
        for row in csv.DictReader(source):
            d, u, v = (int(row[s]) for s in ("degree", "u", "v"))
            if d <= 25:
                moduli[d] = (1 << d) | (1 << (u + v)) | (1 << u) | (1 << v) | 1
    return moduli


def surviving_residues(d, modulus):
    """Indicator of the n modulo 2^d-1 for which X^n+X^2+1 has no root in F_(2^d)."""
    q = 1 << d
    period = q - 1
    logarithms = array("i", [-1]) * q
    element = 1
    for i in range(period):
        if logarithms[element] != -1:
            raise ValueError(f"field generator has a short cycle in degree {d}")
        logarithms[element] = i
        element <<= 1
        if element & q:
            element ^= modulus
    if element != 1 or logarithms[0] != -1:
        raise ValueError(f"invalid multiplicative group in degree {d}")

    surviving = bytearray([1]) * period
    seen = bytearray(period)
    element = 1
    for i in range(1, period):
        element <<= 1
        if element & q:
            element ^= modulus
        if seen[i]:
            continue
        # A conjugate gives the same congruence multiplied by the unit 2.
        j = i
        while not seen[j]:
            seen[j] = 1
            j = 2 * j % period
        # For element = g^i, solve i*n = 2*log_g(1+element) modulo the period.
        common = gcd(i, period)
        rhs = 2 * logarithms[element ^ 1]
        if rhs % common == 0:
            step = period // common
            residue = (rhs // common) * pow(i // common, -1, step) % step
            surviving[residue::step] = bytes(common)
    return surviving


def sum_over_residues(tables, base):
    """Sum a product of periodic tables by summing out one prime power at a time."""
    tables = list(tables)
    for p in reversed(list(prime_factors(base))):
        affected = [(m, v) for m, v in tables if m % p == 0]
        tables = [(m, v) for m, v in tables if m % p != 0]
        joint = lcm(*(m for m, _ in affected))
        reduced = joint
        while reduced % p == 0:
            reduced //= p
        values = [0] * reduced
        for a in range(joint):
            values[a % reduced] += prod(v[a % m] for m, v in affected)
        tables.append((reduced, values))
    return prod(v[0] for _, v in tables)


def sieve_densities(through):
    # These fields contain every binary field of degree at most 'through', up to isomorphism.
    degrees = range(max(2, through // 2 + 1), through + 1)
    periods = [(1 << d) - 1 for d in degrees]
    base = lcm(*(gcd(a, b) for a, b in combinations(periods, 2)))
    moduli = field_polynomials()
    all_tables, unit_tables = [], []
    all_count, unit_count = base, totient(base)
    for d, period in zip(degrees, periods):
        common = gcd(period, base)
        surviving = surviving_residues(d, moduli[d])
        counts = [surviving[a::common].count(1) for a in range(common)]
        all_tables.append((common, counts))
        all_count *= period // common
        for p in prime_factors(period):
            surviving[::p] = bytes(period // p)
        counts = [surviving[a::common].count(1) for a in range(common)]
        unit_tables.append((common, counts))
        unit_count *= totient(period) // totient(common)

    # The common residue makes every choice of local extensions compatible by CRT.
    all_fraction = Fraction(sum_over_residues(all_tables, base), all_count)
    prime_fraction = Fraction(sum_over_residues(unit_tables, base), unit_count)
    return Fraction(1, 8) + (1 - all_fraction) / 4, (1 - prime_fraction) / 2


def dilation_bound():
    """Upper bound on the density loss from even taps 2d with d > 1."""
    limit, height, scale = 1 << 20, 1 << 14, 10**12
    smallest = array("I", range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if smallest[p] == p:
            for k in range(p * p, limit + 1, p):
                if smallest[k] == k:
                    smallest[k] = p

    upper, count = 0, 0
    for p in range(3, limit + 1, 2):
        if smallest[p] != p:
            continue
        order = remaining = p - 1
        while remaining > 1:
            ell = smallest[remaining]
            while remaining % ell == 0:
                remaining //= ell
            while order % ell == 0 and pow(2, order // ell, p) == 1:
                order //= ell
        if order % 2 and order < height:
            denominator = p * order
            upper += (scale + denominator - 1) // denominator
            count += 1

    # For odd order h < 2^14, at most h/20 divisors of 2^h-1 exceed 2^20.
    # The dyadic harmonic bound for h >= 2^14 sums to (14+2)/2^15.
    reciprocal_sum = Fraction(upper, scale) + Fraction(height // 2, 20 * limit) + Fraction(16, 1 << 15)
    return reciprocal_sum / 4, count, upper


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=25, metavar="D",
                        help="sieve for roots in all binary fields of degrees up to D (2 to 25)")
    args = parser.parse_args()
    if not 2 <= args.through <= 25:
        parser.error("choose a maximum field degree between 2 and 25")
    primitive, prime_degrees = sieve_densities(args.through)
    loss, count, upper = dilation_bound()
    if args.through == 25 and not (primitive > Fraction(35756, 100000) and
                                   prime_degrees > Fraction(47742, 100000) and
                                   primitive - loss > Fraction(34101, 100000)):
        raise ArithmeticError("the computed fractions fall short of the stated density bounds")
    print(f"No primitive trinomial, lower density at least {primitive} ({float(primitive):.10%}).")
    print(f"No irreducible trinomial among prime degrees, lower relative density at least "
          f"{prime_degrees} ({float(prime_degrees):.10%}).")
    print(f"For {count} small primes of odd order the rounded reciprocal sum is {upper}/10^12. "
          f"The density loss including both tails is at most {loss}.")
    print(f"No irreducible trinomial, lower density at least {primitive - loss} "
          f"({float(primitive - loss):.10%}).")


if __name__ == "__main__":
    main()
