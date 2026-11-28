"""Verify the cubic sine moment giving a degree-1229 failure by 587 conjugates."""

import argparse
import json
from fractions import Fraction
from math import gcd

from flint import ctx, fmpz, fmpz_mod_poly_ctx

from check_1229_collision_ranks import LEAST, check_frequencies, derivative_product
from check_1229_collision_ranks import root_product_polynomial, sqrt_upper
from check_degree_1229 import COFACTOR, N
from check_factor_base import DATA


ARCHIVE = DATA / "degree-1229-cubic-frequency-products.json"


def signed_orbit(x, degree, modulus):
    """Give the key of the two signed dyadic orbits and the orientation of x."""
    power = int(pow(x, degree, modulus))
    if 2*power > modulus:
        return int(modulus)-power, -1
    return power, 1


def cubic_coefficients(degree, modulus):
    """Expand the cube of sum_i (X^(2^i)-X^(-2^i)), once per dyadic orbit."""
    coefficients = {}
    powers = [pow(fmpz(2), i, modulus) for i in range(degree)]

    def add(exponent, multiplicity):
        key, sign = signed_orbit(exponent, degree, modulus)
        if key:
            coefficients[key] = coefficients.get(key, 0) + sign*multiplicity

    # All three positions equal, then exactly two equal at position zero.
    add(fmpz(3), 1)
    add(fmpz(1), -3)
    for y in powers[1:]:
        add(y+2, 3)
        add(y-2, 3)
        add(y, -6)

    # Each three-position orbit has one lexicographically maximal cyclic gap triple.
    triples = 0
    for a in range((degree+2)//3, degree-1):
        for b in range(max(1, degree-2*a), min(a, degree-a-1)+1):
            c = degree-a-b
            if (a, b, c) < max((b, c, a), (c, a, b)):
                continue
            triples += 1
            y, z = powers[a], powers[a+b]
            add(1+y+z, 6)
            add(1+y-z, -6)
            add(1-y+z, -6)
            add(1-y-z, 6)
    if 6*triples != (degree-1)*(degree-2):
        raise ArithmeticError("the cyclic gap triples do not cover all three-position subsets")
    return {key: value for key, value in coefficients.items() if value}


def check_small_primes():
    # Independently convolve the full integer coefficient arrays in Z[X]/(X^p-1).
    for degree, prime in ((5, 31), (7, 127), (11, 23), (11, 89), (13, 8191)):
        modulus = fmpz(prime)
        expanded = cubic_coefficients(degree, modulus)
        powers = [pow(2, i, prime) for i in range(degree)]
        terms = [0]*prime
        terms[0] = 1
        for _ in range(3):
            result = [0]*prime
            for x, value in enumerate(terms):
                if value:
                    for h in powers:
                        result[(x+h) % prime] += value
                        result[(x-h) % prime] -= value
            terms = result
        for x, value in enumerate(terms):
            key, sign = signed_orbit(fmpz(x), degree, modulus)
            if value != sign*expanded.get(key, 0):
                raise ArithmeticError(f"cubic coefficient at {x} differs in modulus {prime}")


def modular_product(values, modulus):
    product = fmpz(1)
    for value in values:
        product = product*int(value) % modulus
    return int(product)


def cross_product(base, additional, modulus):
    """Evaluate the base root product at the additional points in smaller blocks."""
    divisor = root_product_polynomial(additional, modulus)
    remainder = fmpz_mod_poly_ctx(modulus).one()
    block = 32768
    for start in range(0, len(base), block):
        factor = root_product_polynomial(base[start:start+block], modulus)
        remainder = (remainder*factor) % divisor
    return modular_product(remainder.multipoint_evaluate(additional), modulus)


def check_archive(replay):
    record = json.loads(ARCHIVE.read_text())
    c = fmpz(COFACTOR)
    cutoff, last = record['base_harmonic'], record['last_harmonic']
    if (record['degree'], cutoff, last) != (N, 4095, 65535):
        raise ValueError("incorrect degree or harmonic range")
    coefficients = cubic_coefficients(N, c)
    base = set(coefficients)
    additional = []
    total = Fraction(0)
    for t in range(1, last+1, 2):
        key, sign = signed_orbit(fmpz(t), N, c)
        total += Fraction(sign*coefficients.get(key, 0), t)
        if t <= cutoff:
            base.add(key)
        elif key not in coefficients:
            additional.append(key)
    if (len(coefficients) != record['cubic_orbits'] or len(base) != record['base_orbits'] or
            len(additional) != record['additional_orbits'] or coefficients[1] != record['coefficient_at_one'] or
            sum(v*v for v in coefficients.values()) != record['sum_squared_coefficients'] or
            total != Fraction(*record['harmonic_sum'])):
        raise ArithmeticError("the enumerated orbits, moments or harmonic sum differ from the archive")
    products = ['unit_product', 'derivative_product', 'cross_product']
    if any(gcd(record[name], COFACTOR) != 1 for name in products):
        raise ArithmeticError("a frequency product has a common factor with the cofactor")
    if replay:
        points = [fmpz(key)**2 % c for key in base]
        cubic = [fmpz(key)**2 % c for key in coefficients]
        extra = [fmpz(key)**2 % c for key in additional]
        if modular_product(points, c) != record['unit_product']:
            raise ArithmeticError("incorrect product of base frequencies")
        if derivative_product(points, c) != record['derivative_product']:
            raise ArithmeticError("incorrect base derivative product")
        if cross_product(cubic, extra, c) != record['cross_product']:
            raise ArithmeticError("incorrect additional-frequency cross product")
    return last, total, coefficients[1], record['sum_squared_coefficients']


def check_bounds(bound, last, harmonic_sum, linear, squares):
    pi_lower, pi_upper = Fraction(31415, 10000), Fraction(31416, 10000)
    second = Fraction(N, 2)
    fourth = Fraction(-N*linear, 8)
    sixth = Fraction(N*squares, 32)
    # Truncate the sampled sign function and project its residual off the first harmonic.
    epsilon = (Fraction(2*N*last**2, LEAST**2) +
               2/pi_lower*sqrt_upper(Fraction(N, last-1)) +
               N*sqrt_upper(4/(pi_lower**2*bound) + Fraction(1, LEAST)))
    delta = N*(pi_upper/(4*LEAST**2) + 2*(N-1)/(pi_lower*bound))
    if harmonic_sum >= 0 or fourth <= 0:
        raise ArithmeticError("unexpected sign in the cubic projection")
    correlation = (-N*harmonic_sum/(2*pi_upper) - fourth/second*delta
                   - epsilon*sqrt_upper(sixth-fourth**2/second))
    absolute_third = sqrt_upper(second*fourth)
    for cutoff, minimum in ((53, 59*10**9), (51, 29*10**11), (49, 10**13)):
        margin = correlation-cutoff*absolute_third
        if margin <= 0:
            raise ArithmeticError("the projected correlation is too small")
        count = Fraction(LEAST, 2)*(margin/(N*sqrt_upper(sixth)))**2
        if count <= minimum:
            raise ArithmeticError("insufficient light subsets")
        rank = (N-cutoff-2)//2
        print(f"More than {minimum:,} subsets of at most {rank} conjugates have product one.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frequencies', action='store_true', help='also recompute the three modular products')
    parser.add_argument('--threads', type=int, default=1, help='FLINT threads for the modular products')
    args = parser.parse_args()
    if args.threads < 1:
        parser.error('the thread count must be positive')
    ctx.threads = args.threads
    check_small_primes()
    check_bounds(check_frequencies(False), *check_archive(args.frequencies))
