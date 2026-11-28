"""Check the degree-1229 odd-exponent bound and the residue counts used in its sieve."""

from collections import Counter
from fractions import Fraction
from math import comb, isqrt

from check_1229_wheel import EXTENDED_BOUND
from check_degree_1229 import COFACTOR, GROUP, N, PRIMES
from check_factor_base import irreducible, polynomial
from make_witnesses import gcd, mask_product, remainder, square_mod


def check_residue_counts():
    # Test both choices of leading parity. Fix B and vary all free coefficients of A.
    for n in (9, 10, 11, 12):
        even_free = (n - 1) // 2
        top = 1 << (n // 2)
        a_squares = []
        for bits in range(1 << even_free):
            a = (bits << 1) | 1
            if n % 2 == 0:
                a |= top
            a_squares.append(mask_product(a, a))
        moduli = []
        for d in range(1, (1 << (even_free + 1)), 2):
            derivative = sum(1 << (i - 1) for i in range(1, d.bit_length(), 2) if d >> i & 1)
            if gcd(d, derivative) == 1:
                counts = Counter(remainder(squared, d) for squared in a_squares)
                moduli.append((d, counts))
        for bits in range(1 << (n // 2)):
            b = bits | top if n % 2 else bits
            odd_part = mask_product(b, b) << 1
            for d, counts in moduli:
                expected = 1 << (even_free - (d.bit_length() - 1))
                if counts[remainder(odd_part, d)] != expected:
                    raise ArithmeticError(f"incorrect divisor frequency in degree {n}")


def check_trace_prefixes():
    for n in (9, 10, 11, 12):
        for f in range(2**n + 1, 2**(n + 1), 2):
            if not irreducible(polynomial(f)):
                continue
            first_odd = next(i for i in range(1, n + 1, 2) if f >> i & 1)
            inverse = f >> 1  # X * inverse = 1 modulo f.
            power = 1
            for j in range(1, first_odd + 1):
                power = remainder(mask_product(power, inverse), f)
                conjugate, trace = power, 0
                for _ in range(n):
                    trace ^= conjugate
                    conjugate = square_mod(conjugate, f)
                if trace != int(j == first_odd):
                    raise ArithmeticError(f"incorrect trace at power {j} modulo {f:#x}")


def check_1229():
    slots = 17
    odd_bound = 11
    gaps = (N + 1) // 2 - slots
    modulus_degree = 2 * gaps - 1
    even_free = (N - 1) // 2
    sieve_level = even_free // 2
    prime_floor = EXTENDED_BOUND + 1
    if prime_floor**16 <= COFACTOR:
        raise ArithmeticError("insufficient lower bound on the cofactor primes")
    excluded_density = sum((Fraction(1, p) for p in PRIMES), Fraction(15, prime_floor))
    if excluded_density >= Fraction(1, 20000):
        raise ArithmeticError("known and possible primes exceed the density allowance")
    main = Fraction(19999 * GROUP, 20000 * 2**gaps)
    error = (1 + len(PRIMES) + 15) * modulus_degree * (isqrt(2**N) + 1)
    # The leading odd term is compulsory. The other slots are free.
    heavy = sum(comb(slots - 1, j) for j in range(odd_bound, slots))
    heavy_irreducibles = Fraction(3 * 2**even_free * heavy, sieve_level + 3)
    count = (main - error) / N - heavy_irreducibles
    if (gaps, modulus_degree, heavy, sieve_level) != (598, 1195, 6885, 307):
        raise ArithmeticError("unexpected odd-slot or sieve parameters")
    if count <= 2**617:
        raise ArithmeticError("insufficient primitive-polynomial count")
    print("More than 2^617 primitive polynomials have at most eleven odd-degree terms.")
    print(f"Every odd exponent lies between {2*gaps + 1} and {N}.")


if __name__ == "__main__":
    check_residue_counts()
    check_trace_prefixes()
    check_1229()
