"""Certify two sparse primitive polynomials using norms to their maximal subfields."""

import argparse
import json
import subprocess
from math import gcd, lcm, prod
from pathlib import Path

from flint import fmpz, nmod_poly

from check_product_range import certified_primes, prime_index_powers
from check_two_block_orders import multiplicity_bounds


DATA = Path(__file__).resolve().parents[1] / "data"
TABLES = {
    3415: ("mersenne-3201-3456.json", "mersenne-3201-3456-prime-certificates.json.gz"),
    9583: ("mersenne-complementary-width-extra.json", "mersenne-complementary-width-prime-certificates.json.gz"),
}


def verify_norm_embeddings(support, masks, gp):
    """Verify irreducibility and the given annihilating polynomial at each norm."""
    n = support[-1]
    if any(m.bit_length() != d+1 for d, m in masks.items()):
        raise ValueError(f"incorrect norm polynomial degrees at degree {n}")
    # PARI proves irreducibility of the large polynomial and checks the two embeddings.
    terms = "+".join(f"x^{i}" for i in support)
    checks = [f'if(subst(Pol(binary({masks[d]})),x,r^((2^{n}-1)/(2^{d}-1)))!=0,'
              f'error("norm polynomial in degree {d}"));' for d in masks]
    program = (f'check()={{my(f=Mod(1,2)*({terms}),r);'
               'if(!polisirreducible(f),error("reducible input"));r=ffgen(f,\'z);'
               + "".join(checks) + 'print("verified")};\niferr(check(),E,print(E);quit(1));\n')
    result = subprocess.run([gp, "-fq", "-s", "256M"], input=program, text=True,
                            capture_output=True, check=False)
    if result.returncode or result.stderr or result.stdout.splitlines() != ["verified"]:
        raise ArithmeticError(f"norm embedding check failed in degree {n}: {result.stderr}{result.stdout}")


def verify_norm_witness(support, masks, factor_lists, gp):
    """Verify both norm embeddings and their full orders in the small fields."""
    if set(masks) != set(factor_lists):
        raise ValueError("norm polynomials and factor lists describe different subfields")
    verify_norm_embeddings(support, masks, gp)
    # Each remaining primitive-element test takes place in the smaller binary quotient.
    x = nmod_poly([0, 1], 2)
    for d in masks:
        order = 2**d - 1
        primes = sorted(set(factor_lists[d]))
        if not all(fmpz(s).is_prime() for s in primes):
            raise ArithmeticError(f"composite factor of the degree-{d} norm order")
        remainder = order
        for s in primes:
            while remainder % s == 0:
                remainder //= s
        f = nmod_poly([(masks[d] >> i) & 1 for i in range(d+1)], 2)
        if (remainder != 1 or x.pow_mod(order, f) != 1 or
                any(value == 1 for _, value in prime_index_powers(x, order, primes, f))):
            raise ArithmeticError(f"degree-{d} norm failed primitivity")


def check(n, row, gp):
    support = row["exponents"]
    p, q = row["degree_primes"]
    if (len(support) != 5 or support != sorted(set(support)) or support[0] != 0
            or support[-1] != n or gcd(*support) != 1 or not p < q
            or any(n % s or not fmpz(s).is_prime() for s in (p, q))):
        raise ValueError(f"invalid sparse support or degree primes in degree {n}")
    k, _ = multiplicity_bounds(support)
    if k >= q:
        raise ValueError("the quotient bound does not force a new order factor")
    degrees = [n//p, n//q]
    masks = {int(d): int(value, 16) for d, value in row["norm_polynomials"].items()}
    a, b = (2**d - 1 for d in degrees)
    m = 2**n - 1
    large = m // lcm(a, b)
    if m != lcm(a, b)*large or gcd(large, a*b) != 1:
        raise ValueError("the two maximal subfields do not account for the complementary part")
    factors_file, certs_file = TABLES[n]
    factors = json.loads((DATA / factors_file).read_text())[str(n)]
    if prod(factors) != m or large not in factors or certified_primes(DATA / certs_file, {large}, gp) != {large}:
        raise ArithmeticError("the remaining prime lacks a valid primality proof")

    verify_norm_witness(support, masks, {d: [s for s in factors if (2**d-1) % s == 0]
                                         for d in degrees}, gp)
    print(f"Degree {n} is primitive. K={k} forces the {len(str(large))}-digit prime, "
          f"and both norms to degrees {degrees[0]} and {degrees[1]} are primitive.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp")
    args = parser.parse_args()
    rows = json.loads((DATA / "two-subfield-norms.json").read_text())
    if set(rows) != {str(n) for n in TABLES}:
        parser.error("incomplete norm records")
    for n in TABLES:
        check(n, rows[str(n)], args.gp)
