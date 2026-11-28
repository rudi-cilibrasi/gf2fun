"""Verify sparse witnesses against a table of completely factored binary field orders."""

import argparse
import csv
import io
import json
import subprocess
import sys
from math import lcm, prod
from pathlib import Path

from flint import fmpz, nmod_poly

from check_factor_base import modulus
from check_primo_certificate import check_primo
from check_product_range import certified_primes, prime_index_powers, verify, verify_primitive_modulus


DATA = Path(__file__).resolve().parents[1] / "data"
X = nmod_poly([0, 1], 2)


def check_trinomials(n, row, factors, ntl):
    if n % 8 == 0:
        # Swan's theorem excludes irreducible trinomials in these degrees.
        if row["irreducible_taps"] or row["primitive_taps"]:
            raise ValueError(f"unexpected trinomial in a degree divisible by eight: {n}")
        return []
    taps = row["irreducible_taps"]
    if taps != sorted(set(taps)) or any(not 0 < a <= n // 2 for a in taps):
        raise ValueError(f"invalid trinomial representatives in degree {n}")
    order = (1 << n) - 1
    primitive = []
    for a in taps:
        f = X**n + X**a + 1
        if (X.pow_mod(1 << n, f) != X or
                any((X.pow_mod(1 << (n // int(p)), f) + X).gcd(f) != 1
                    for p, _ in fmpz(n).factor())):
            raise ValueError(f"reducible trinomial in degree {n} with tap {a}")
        if all(v != 1 for _, v in prime_index_powers(X, order, sorted(set(factors)), f)):
            primitive.append(a)
    if primitive != row["primitive_taps"]:
        raise ValueError(f"incorrect primitive trinomial list in degree {n}")
    if ntl:
        line = " ".join(map(str, [n, len(factors), *factors])) + "\n"
        result = subprocess.run([ntl], input=line, text=True, capture_output=True, check=True)
        [census] = csv.DictReader(io.StringIO(result.stdout))
        if (int(census["degree"]) != n or list(map(int, census["irreducible_taps"].split())) != taps
                or list(map(int, census["primitive_taps"].split())) != primitive):
            raise ValueError(f"exhaustive trinomial census disagreement in degree {n}")
    return primitive


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for ECPP certificates")
    parser.add_argument("--ntl", help="compiled scripts/prime_degree_trinomials.cpp for an exhaustive census")
    parser.add_argument("--table", type=Path, default=DATA / "composite-order-witnesses.json",
                        help="JSON table of witnesses and order factorizations")
    parser.add_argument("--degree", type=int, help="verify only this degree from the table")
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    rows = json.loads(args.table.read_text())
    if args.degree is not None:
        if str(args.degree) not in rows:
            parser.error(f"degree {args.degree} is absent from the witness table")
        rows = {str(args.degree): rows[str(args.degree)]}
    primes = {p for row in rows.values() for p in row["order_factors"]}
    certified = certified_primes(DATA / "composite-order-prime-certificates.json.gz", primes, args.gp)
    for degree, row in rows.items():
        if "primo_certificate" in row:
            p = max(row["order_factors"])
            check_primo(DATA / f"degree-{degree}-primality.cert.gz", p, args.gp)
            certified.add(p)
    if not all(fmpz(p).is_prime() for p in primes - certified):
        raise ValueError("composite factor in order data")
    for degree, row in rows.items():
        n = int(degree)
        factors = row["order_factors"]
        order = (1 << n) - 1
        if any(p < 2 for p in factors) or prod(factors) != order:
            raise ValueError(f"incomplete factorization in degree {n}")
        if "primitive_part_small_factors" in row:
            lower = lcm(*((1 << (n // int(p))) - 1 for p, _ in fmpz(n).factor()))
            small = row["primitive_part_small_factors"]
            if any(p not in factors for p in small) or lower * max(factors) * prod(small) != order:
                raise ValueError(f"incorrect cyclotomic part in degree {n}")
        if "pentanomial_taps" in row:
            taps = row["pentanomial_taps"]
            if len(taps) != 3 or taps != sorted(set(taps)) or not 0 < taps[0] <= taps[-1] < n:
                raise ValueError(f"invalid pentanomial in degree {n}")
            verify_primitive_modulus(modulus(n, taps), factors)
        else:
            verify(n, *row["complementary_taps"], factors, symmetric=True)
        primitive = check_trinomials(n, row, factors, args.ntl)
        print(f"Degree {n}: primitive pentanomial verified, primitive trinomial taps {primitive}.",
              flush=True)


if __name__ == "__main__":
    main()
