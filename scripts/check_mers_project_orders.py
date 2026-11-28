"""Prove the exact root orders of the sparse witnesses in the Mers Project table."""

import argparse
import csv
import gzip
import json
import shutil
import subprocess
import sys
import tempfile
import urllib.request
from math import gcd, prod
from pathlib import Path

from flint import fmpz

from check_composite_orders import check_trinomials
from check_factor_base import modulus, polynomial
from check_primo_certificate import check_primo
from check_product_range import prime_index_powers, verify_primitive_modulus


DATA = Path(__file__).resolve().parents[1] / "data"


def prove_with_certificate(p, proof, gp, cache):
    if isinstance(proof, dict):
        multiplier = proof["pocklington_cofactor"]
        base = proof["base"]
        if not 0 < multiplier < p or not 1 < base < p:
            raise ValueError("invalid Pocklington cofactor or base")
        q, remainder = divmod(p - 1, multiplier)
        if (remainder or q*q <= p or pow(base, p - 1, p) != 1 or
                gcd(pow(base, multiplier, p) - 1, p) != 1):
            raise ValueError("Pocklington step failed")
        p, identifier = q, proof["child_certificate"]
    else:
        identifier = proof
    if not isinstance(identifier, str) or not identifier.isdecimal():
        raise ValueError("invalid PRIMO certificate identifier")
    name = f"{identifier}.cert.gz"
    local = DATA / "mers-project-primality" / name
    if local.is_file():
        check_primo(local, p, gp)
        return
    if cache is None:
        raise FileNotFoundError(f"external certificate {identifier} requires --fetch-to DIRECTORY")
    cached = cache / name
    if cached.is_file():
        check_primo(cached, p, gp)
        return
    cache.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=cache) as temporary:
        path = Path(temporary) / name
        with urllib.request.urlopen(f"https://factordb.com/cert/{identifier}", timeout=60) as source:
            with gzip.open(path, "wb") as archive:
                shutil.copyfileobj(source, archive)
        check_primo(path, p, gp)
        path.replace(cached)


def verify_trinomial_order(n, tap, index, factors):
    d = gcd(n, tap)
    bound = d * ((1 << (n // d)) - 1)
    if type(index) is not int or not 1 <= index <= bound:
        raise ValueError(f"invalid index in the dilation bound in degree {n}")
    order, remainder = divmod(bound, index)
    if remainder or ((1 << n) - 1) % order:
        raise ValueError(f"invalid proposed trinomial order in degree {n}")
    x = polynomial(2)
    f = modulus(n, [tap])
    primes = sorted({p for p in factors if order % p == 0})
    if x.pow_mod(order, f) != 1 or any(z == 1 for _, z in prime_index_powers(x, order, primes, f)):
        raise ValueError(f"incorrect trinomial order in degree {n} at tap {tap}")


def minimum_weight(n, row, gp):
    if len(row["taps"]) == 1:
        return 3
    if "primitive_trinomial_tap" in row:
        tap = row["primitive_trinomial_tap"]
        if not 0 < tap <= n // 2:
            raise ValueError(f"invalid extra trinomial in degree {n}")
        verify_primitive_modulus(modulus(n, [tap]), row["order_factors"])
        return 3
    if n % 8 == 0:
        return 5
    if "trinomial_divisor_hex" in row:
        divisor = polynomial(int(row["trinomial_divisor_hex"], 16))
        if (n % 8 not in (3, 5) or not 0 < divisor.degree() < n or
                modulus(n, [2]) % divisor != 0):
            raise ValueError(f"invalid divisor of the exceptional trinomial in degree {n}")
        return 5
    if "dilated_trinomial_taps" in row:
        taps = row["dilated_trinomial_taps"]
        # Compare all reciprocal representatives with an independent PARI census.
        command = (f"n={n};t=Mod(1,2)*x;f=t^n+1;v=List();"
                   "for(k=1,n\\2,if(polisirreducible(f+t^k),listput(v,k)));print(Vec(v));\n")
        result = subprocess.run([gp, "-qf"], input=command, text=True, capture_output=True, check=True)
        if (result.stderr.strip() or json.loads(result.stdout) != taps or
                any(gcd(n, k) == 1 for k in taps)):
            raise ValueError(f"trinomial census disagreement in degree {n}")
        for k in taps:
            verify_trinomial_order(n, k, 1, row["order_factors"])
        return 5
    return None


def verify(n, row, proven, args):
    taps = row["taps"]
    if (len(taps) not in (1, 3) or taps != sorted(set(taps)) or
            not all(type(t) is int and 0 < t < n for t in taps)):
        raise ValueError(f"invalid sparse polynomial in degree {n}")
    factors = row["order_factors"]
    if (not factors or not all(type(p) is int and p > 1 for p in factors)
            or factors != sorted(factors) or prod(factors) != (1 << n) - 1):
        raise ValueError(f"incomplete field order in degree {n}")
    f = modulus(n, taps)
    if args.powers_only:
        verify_primitive_modulus(f, factors)
        print(f"Degree {n}, factor product, full power and {len(set(factors))} "
              "factor-index powers verified. Primality checks skipped.", flush=True)
        return
    for index, proof in row["primo_certificates"].items():
        i = int(index)
        if not 0 <= i < len(factors) or str(i) != index:
            raise ValueError(f"invalid certificate reference in degree {n}")
        p = factors[i]
        if p not in proven:
            prove_with_certificate(p, proof, args.gp, args.fetch_to)
            proven.add(p)
    for p in set(factors) - proven:
        if not fmpz(p).is_prime():
            raise ValueError(f"composite order factor in degree {n}")
        proven.add(p)
    verify_primitive_modulus(f, factors)
    weight = minimum_weight(n, row, args.gp)
    detail = f" Minimum primitive weight {weight}." if weight is not None else ""
    print(f"Degree {n}, interior exponents {taps}, full order verified "
          f"with {len(set(factors))} distinct prime divisors.{detail}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, action="append", help="select a degree, repeatable")
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for primality proofs")
    parser.add_argument("--table", type=Path, default=DATA / "mers-project-sparse-orders.json")
    parser.add_argument("--fetch-to", type=Path, metavar="DIRECTORY",
                        help="download external PRIMO certificates and cache verified chains here")
    parser.add_argument("--powers-only", action="store_true",
                        help="check the factor product and polynomial powers only, omitting primality proofs")
    parser.add_argument("--trinomial-census", metavar="NTL_PROGRAM",
                        help="also replay the archived trinomial lists with prime_degree_trinomials.cpp")
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    rows = json.loads(args.table.read_text())
    selected = args.degree or sorted(map(int, rows))
    if args.trinomial_census:
        census = {}
        with (DATA / "mers-project-trinomial-census.csv").open() as source:
            for row in csv.DictReader(source):
                census[int(row["degree"])] = {
                    "irreducible_taps": list(map(int, row["irreducible_taps"].split())),
                    "primitive_taps": list(map(int, row["primitive_taps"].split())),
                }
    proven = set()
    for n in selected:
        if str(n) not in rows:
            parser.error(f"degree {n} is absent from the table")
        if args.trinomial_census and n not in census:
            parser.error(f"degree {n} is absent from the trinomial census")
        verify(n, rows[str(n)], proven, args)
        if args.trinomial_census:
            check_trinomials(n, census[n], rows[str(n)]["order_factors"], args.trinomial_census)
            indices = rows[str(n)].get("trinomial_indices_in_dilation_bound", {})
            exceptions = set(census[n]["irreducible_taps"]) - set(census[n]["primitive_taps"])
            if set(map(int, indices)) != exceptions:
                raise ValueError(f"incomplete list of imprimitive trinomial orders in degree {n}")
            for tap, index in indices.items():
                verify_trinomial_order(n, int(tap), index, rows[str(n)]["order_factors"])
            detail = "replayed with the supplied factors" if args.powers_only else "verified"
            print(f"Degree {n}, both archived trinomial lists {detail}.", flush=True)


if __name__ == "__main__":
    main()
