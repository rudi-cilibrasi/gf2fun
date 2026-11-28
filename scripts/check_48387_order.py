"""Verify the factorization of 2^48387-1 and the exclusion of all degree-48387 trinomials."""

import argparse
import json
import sys
from math import gcd, prod
from pathlib import Path

from flint import fmpz

from check_factor_base import modulus
from check_primo_certificate import check_primo
from check_product_range import prime_index_powers


DATA = Path(__file__).resolve().parents[1] / "data"


def cyclotomic_factor():
    x = 1 << 127
    y = 1 << 16129
    n, remainder = divmod(y*y + y + 1, x*x + x + 1)
    if remainder:
        raise ArithmeticError("the cyclotomic quotient has a remainder")
    return n


def verify_residue_prime(n, record, gp):
    powers = record["predecessor_prime_powers"]
    primes = [p for p, e in powers]
    if (primes != sorted(set(primes)) or not primes or
            any(type(p) is not int or p < 2 or type(e) is not int or e < 1 for p, e in powers)):
        raise ValueError("invalid prime powers in the predecessor divisor")
    part = prod(p**e for p, e in powers)
    if n <= 2 or (n - 1) % part:
        raise ValueError("the claimed predecessor divisor does not divide N-1")
    identifier = record["largest_predecessor_prime_certificate"]
    if not isinstance(identifier, str) or not identifier.isdecimal():
        raise ValueError("invalid PRIMO certificate identifier")
    check_primo(DATA / "mers-project-primality" / (identifier + ".cert.gz"), primes[-1], gp)
    if not all(fmpz(p).is_prime() for p in primes[:-1]):
        raise ValueError("the predecessor factorization includes a composite")

    # The order of the base modulo every prime divisor of n contains all of part.
    base, modulus = fmpz(record["base"]), fmpz(n)
    if not 1 < base < modulus or pow(base, n - 1, modulus) != 1:
        raise ValueError("the full modular power failed")
    for p, value in prime_index_powers(base, n - 1, primes, modulus, power_mod=pow):
        if gcd(value - 1, n) != 1:
            raise ValueError(f"the prime-index power for {p} failed")

    # For a factor 1 + part*x, the stored polynomial must vanish modulo that
    # factor. Its norm bound and parity exclude every small positive x.
    cubic = record["cubic"]
    if len(cubic) != 4 or any(type(c) is not int for c in cubic) or not cubic[-1]:
        raise ValueError("invalid cubic")
    root = -pow(part, -1, n) % n
    if sum(c * pow(root, j, n) for j, c in enumerate(cubic)) % n:
        raise ValueError("the cubic does not vanish at the prescribed residue")
    bound = n // part**3
    norm = sum(abs(c) * bound**j for j, c in enumerate(cubic))
    if norm >= part or cubic[0] % 2 != 1 or sum(cubic) % 2 != 1:
        raise ValueError("the cubic does not exclude every small factor")

    # If both factors have the form 1 + part*x with x <= part, their two
    # multipliers have a prescribed sum modulo part and a square discriminant.
    quotient = (n - 1) // part
    discriminants = []
    for total in range(quotient % part, 2*part + 1, part):
        if total < 2:
            continue
        delta = total**2 - 4*((quotient - total) // part)
        discriminants.append(delta % 5)
        if delta % 5 in (0, 1, 4):
            raise ValueError("the discriminant test modulo five did not exclude a factorization")
    print(f"Certified the {len(str(n))}-digit prime. The predecessor divisor has "
          f"{part.bit_length()} bits, the cubic norm has {norm.bit_length()} bits, "
          f"and the discriminants modulo five are {discriminants}.", flush=True)


def full_factorization(largest, record, gp):
    rows = json.loads((DATA / "composite-order-witnesses.json").read_text())
    inherited = rows["16129"]["order_factors"]
    other = record["additional_order_factors"]
    if prod(inherited) != (1 << 16129) - 1 or prod(other) != (1 << 254) + (1 << 127) + 1:
        raise ValueError("incorrect cyclotomic factorization")
    child = max(inherited)
    check_primo(DATA / "degree-16129-primality.cert.gz", child, gp)
    if not all(fmpz(p).is_prime() for p in (set(inherited) | set(other)) - {child}):
        raise ValueError("a remaining order factor is composite")
    factors = sorted([*inherited, *other, largest])
    group_order = (1 << 48387) - 1
    if prod(factors) != group_order or gcd(48387, group_order) != 1:
        raise ValueError("incorrect group order or exponent gcd")
    if 48387 % 8 != 3 or modulus(48387, [2]) % modulus(3, [2]) != 0:
        raise ValueError("the exceptional Swan trinomial is not excluded")
    print(f"Verified all {len(set(factors))} distinct prime divisors of 2^48387-1 "
          "and the cubic divisor excluding the last trinomial.", flush=True)
    return factors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for the child certificate")
    parser.add_argument("--prime-only", action="store_true", help="only verify the 9,635-digit prime")
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    record = json.loads((DATA / "degree-48387-order-prime.json").read_text())
    largest = cyclotomic_factor()
    verify_residue_prime(largest, record, args.gp)
    if not args.prime_only:
        full_factorization(largest, record, args.gp)


if __name__ == "__main__":
    main()
