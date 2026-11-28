"""Verify the exceptional root orders and the archived cyclotomic weight spectra."""

import argparse
import json
import subprocess
import sys
from itertools import compress
from math import gcd
from pathlib import Path

from flint import fmpz

from check_primo_certificate import check_primo
from check_product_range import certified_primes


DATA = Path(__file__).resolve().parents[1] / "data"
# Interior taps of an irreducible defining polynomial, and the ECPP archive if needed.
FIELDS = {
    1637: ([26, 51, 77], None),
    3359: ([15, 20, 35], "mersenne-3201-3456-prime-certificates.json.gz"),
    4243: ([435, 870, 3808], "mersenne-prime-degrees-ecpp.json.gz"),
    17029: ([1, 2, 560], "degree-17029-primality.cert.gz"),
}
# For these Mers Project witnesses the small-prime order bound uses trial division.
MERS_DEGREES = (28759, 28771)
TRIAL_BOUND = 1 << 44


def prime_divisors_through(n, bound):
    """Sieve primes q dividing 2^n-1 through bound for an odd prime degree n."""
    if n < 3 or n % 2 == 0 or not fmpz(n).is_prime():
        raise ValueError("the progression sieve requires an odd prime degree")
    step = 2 * n
    last = (bound - 1) // step
    # An odd order of 2 implies that 2 is a square modulo q, so q is 1 or 7 modulo 8.
    exclusions = [(4, k) for k in range(4) if (1 + step * k) % 8 not in (1, 7)]
    for p in range(3, min(1024, step + 1), 2):
        if fmpz(p).is_prime() and step % p:
            exclusions.append((p, -pow(step, -1, p) % p))
    divisors = []
    block = 1 << 19
    for start in range(1, last + 1, block):
        stop = min(start + block, last + 1)
        allowed = bytearray([1]) * (stop - start)
        for stride, residue in exclusions:
            offset = (residue - start) % stride
            allowed[offset::stride] = bytes((len(allowed) + stride - 1 - offset) // stride)
        for k in compress(range(start, stop), allowed):
            q = 1 + step * k
            if pow(2, n, q) == 1 and fmpz(q).is_prime():
                divisors.append(q)
    return divisors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", default="cyclotomic_weight_census", help="compiled NTL census")
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for the ECPP certificates")
    degrees = [*FIELDS, *MERS_DEGREES]
    parser.add_argument("--degree", choices=degrees, type=int, help="check one degree from the archive")
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    rows = json.loads((DATA / "cyclotomic-weight-spectra.json").read_text())
    if [row["degree"] for row in rows] != degrees:
        raise ValueError("unexpected degree list")
    for row in rows:
        n, s = row["degree"], row["prime"]
        if args.degree is not None and n != args.degree:
            continue
        p, remainder = divmod((1 << n) - 1, s)
        if remainder or p <= s or not fmpz(s).is_prime():
            raise ValueError(f"incorrect group order factors at degree {n}")
        if n in MERS_DEGREES:
            witness = json.loads((DATA / "mers-project-large-orders.json").read_text())[str(n)]
            if (witness["order_factors"] != [s, p] or gcd(s, p) != 1 or
                    prime_divisors_through(n, TRIAL_BOUND) != [s]):
                raise ValueError(f"small prime order census disagreement in degree {n}")
            taps = witness["taps"]
        else:
            taps, archive = FIELDS[n]
            if archive and archive.endswith(".cert.gz"):
                check_primo(DATA / archive, p, args.gp)
            elif archive:
                if certified_primes(DATA / archive, {p}, args.gp) != {p}:
                    raise ValueError(f"missing large-prime proof at degree {n}")
            elif not fmpz(p).is_prime():
                raise ValueError(f"large cofactor is composite at degree {n}")
        mode = ["--check-factors"] if n == 17029 or n in MERS_DEGREES else []
        result = subprocess.run([args.census, *mode, *map(str, [n, s, *taps])], text=True,
                                capture_output=True, check=True)
        if json.loads(result.stdout) != row or row["additive_intersection"] != 0:
            raise ValueError(f"cyclotomic census disagreement at degree {n}")
        minimum = min(map(int, row["weights"]))
        orbit_min = min(minimum, min(map(int, row["translated_weights"])))
        print(f"Degree {n}: all {sum(row['weights'].values())} factors verified. "
              f"Minimum weight {minimum}, six-image minimum {orbit_min}.", flush=True)
        if n in MERS_DEGREES:
            print(f"Every irreducible of weight below {minimum} has a root-order prime "
                  f"exceeding {TRIAL_BOUND}.", flush=True)


if __name__ == "__main__":
    main()
