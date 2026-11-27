"""Prove the exact root orders of the sparse witnesses in the Mers Project table."""

import argparse
import json
import sys
from math import prod
from pathlib import Path

from flint import fmpz

from check_factor_base import modulus
from check_primo_certificate import check_primo
from check_product_range import verify_primitive_modulus


DATA = Path(__file__).resolve().parents[1] / "data"


def verify(n, row, proven, gp):
    taps = row["taps"]
    if (len(taps) not in (1, 3) or taps != sorted(set(taps)) or
            not all(type(t) is int and 0 < t < n for t in taps)):
        raise ValueError(f"invalid sparse polynomial in degree {n}")
    factors = row["order_factors"]
    if (not factors or not all(type(p) is int and p > 1 for p in factors)
            or factors != sorted(factors) or prod(factors) != (1 << n) - 1):
        raise ValueError(f"incomplete field order in degree {n}")
    for index, identifier in row["primo_certificates"].items():
        i = int(index)
        if not 0 <= i < len(factors) or str(i) != index or not identifier.isdecimal():
            raise ValueError(f"invalid certificate reference in degree {n}")
        p = factors[i]
        if p not in proven:
            path = DATA / "mers-project-primality" / f"{identifier}.cert.gz"
            check_primo(path, p, gp)
            proven.add(p)
    for p in set(factors) - proven:
        if not fmpz(p).is_prime():
            raise ValueError(f"composite order factor in degree {n}")
        proven.add(p)
    verify_primitive_modulus(modulus(n, taps), factors)
    print(f"Degree {n}, interior exponents {taps}, full order verified "
          f"with {len(set(factors))} distinct prime divisors.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, action="append", help="select a degree, repeatable")
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for primality proofs")
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    rows = json.loads((DATA / "mers-project-sparse-orders.json").read_text())
    selected = args.degree or sorted(map(int, rows))
    proven = set()
    for n in selected:
        if str(n) not in rows:
            parser.error(f"degree {n} is absent from the table")
        verify(n, rows[str(n)], proven, args.gp)


if __name__ == "__main__":
    main()
