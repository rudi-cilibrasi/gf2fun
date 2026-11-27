"""Verify the two semiprime degrees whose large cyclotomic prime is forced by the scalar-order bound."""

import argparse
import csv
import json
import subprocess
from io import StringIO
from math import gcd, prod
from pathlib import Path

from flint import fmpz

from check_primo_certificate import check_primo
from check_two_subfield_norms import verify_norm_witness


DATA = Path(__file__).resolve().parents[1] / "data"


def check(n, row, gp, trinomials):
    p, q = row["degree_primes"]
    a, b = (1 << p) - 1, (1 << q) - 1
    if not (2 < p < q and p*q == n and n < 3*a and
            all(fmpz(t).is_prime() for t in (p, q, a))):
        raise ValueError(f"scalar-order exclusion failed for degree {n}")
    order = (1 << n) - 1
    large, remainder = divmod(order, a*b)
    if remainder or gcd(large, a*b) != 1 or gcd(a, b) != 1:
        raise ValueError(f"invalid cyclotomic decomposition at degree {n}")
    check_primo(DATA / f"degree-{n}-primality.cert.gz", large, gp)

    factors = {int(k): v for k, v in row["subfield_factors"].items()}
    if set(factors) != {p, q} or any(prod(factors[d]) != (1 << d)-1 for d in factors):
        raise ValueError(f"incomplete subfield factors at degree {n}")
    weights = []
    for witness in row["witnesses"]:
        support = witness["exponents"]
        if (support != sorted(set(support)) or support[0] != 0 or support[-1] != n
                or len(support) not in (3, 5)):
            raise ValueError(f"incorrect sparse support at degree {n}")
        masks = {int(k): int(v, 16) for k, v in witness["norm_polynomials"].items()}
        verify_norm_witness(support, masks, factors, gp)
        weights.append(len(support))
    if not weights:
        raise ValueError(f"missing witnesses at degree {n}")

    primes = [*factors[p], *factors[q], large]
    inputs = " ".join(map(str, [n, len(primes), *primes])) + "\n"
    result = subprocess.run([trinomials], input=inputs, text=True, capture_output=True, check=True)
    rows = list(csv.DictReader(StringIO(result.stdout)))
    expected = " ".join(map(str, row["irreducible_trinomial_taps"]))
    if rows != [{"degree": str(n), "irreducible_taps": expected, "primitive_taps": expected}]:
        raise ArithmeticError(f"trinomial census disagreement for degree {n}")
    minimum = 3 if expected else 5
    if min(weights) != minimum:
        raise ArithmeticError(f"missing witness of minimum weight in degree {n}")
    print(f"Degree {n}: {len(str(large))}-digit prime verified, "
          f"primitive norms in degrees {p} and {q}, minimum weight {minimum}.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp")
    parser.add_argument("--trinomials", required=True, help="compiled scripts/prime_degree_trinomials.cpp")
    args = parser.parse_args()
    rows = json.loads((DATA / "semiprime-scalar-norms.json").read_text())
    if set(rows) != {"5053", "14263"}:
        parser.error("incomplete semiprime norm records")
    for n, row in rows.items():
        check(int(n), row, args.gp, args.trinomials)
