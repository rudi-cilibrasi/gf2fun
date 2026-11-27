"""Certify the minimum largest interior exponent of a primitive degree-4096 pentanomial."""

import argparse
import csv
import gzip
import json
from itertools import combinations
from math import prod

from flint import fmpz

from check_factor_base import DATA, modulus, polynomial
from check_product_range import certified_primes


N = 4096
TAPS = (1, 15, 27)


def check_exclusions():
    with gzip.open(DATA / "degree-4096-small-tap-factors.csv.gz", "rt", newline="") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != ["a", "b", "c", "factor_hex"]:
            raise ValueError("incorrect divisor-table header")
        divisors = {}
        for row in reader:
            taps = tuple(int(row[k]) for k in ("a", "b", "c"))
            if taps in divisors:
                raise ValueError("repeated tap triple")
            divisors[taps] = int(row["factor_hex"], 16)
    for taps in combinations(range(1, 28), 3):
        if taps == TAPS or all(k % 2 == 0 for k in taps):
            continue
        d = polynomial(divisors.pop(taps))
        if not 0 < d.degree() < N or not (modulus(N, taps) % d).is_zero():
            raise ArithmeticError(f"invalid proper divisor at {taps}")
    if divisors:
        raise ValueError("extraneous divisor certificate")


def check_order(gp):
    order = 2**N-1
    factors = json.loads((DATA / "mersenne-3457-4096.json").read_text())[str(N)]
    if len(set(factors)) != 25 or prod(factors) != order:
        raise ValueError("incomplete group factorization")
    covered = certified_primes(DATA / "mersenne-3457-4096-prime-certificates.json.gz", set(factors), gp)
    if any(not fmpz(p).is_prime() for p in set(factors)-covered):
        raise ArithmeticError("composite order factor")
    x, f = polynomial(2), modulus(N, TAPS)
    # Equality at the full exponent and every prime-index inequality give order 2^N-1.
    if x.pow_mod(order, f) != 1 or any(x.pow_mod(order//p, f) == 1 for p in factors):
        raise ArithmeticError("the designated polynomial failed the full-order test")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for the ECPP chain")
    args = parser.parse_args()
    check_exclusions()
    check_order(args.gp)
    print("Of 2,925 degree-4096 pentanomials with all three taps at most 27,")
    print("only the taps (1, 15, 27) are irreducible. Their root has order 2^4096-1.")
