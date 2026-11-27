"""Certify sparse primitive polynomials at semiprime degrees using a scalar-order obstruction and two norms."""

import argparse
import csv
import json
import subprocess
from collections import Counter
from io import StringIO
from math import gcd, prod
from pathlib import Path

from flint import fmpz, nmod_poly

from check_primo_certificate import check_primo
from check_two_subfield_norms import verify_norm_witness
from check_subfield_products import contains_binary_plane


DATA = Path(__file__).resolve().parents[1] / "data"


def scalar_counts(binary, p, q, h):
    result = subprocess.run([binary, *map(str, (p, q, h))], text=True,
                            capture_output=True, check=True)
    return list(map(int, result.stdout.split()))


def check_control(binary):
    # All degree-ten roots of order dividing 3*31 lie in the product of these fields.
    x = nmod_poly([0, 1], 2)
    count = sum(f.degree() == 10 and sum(map(int, f)) == 5 for f, _ in (x**93+1).factor()[1])
    if count != 4 or scalar_counts(binary, 2, 5, 3) != [1, 45, 5, 4, count]:
        raise ValueError("scalar pair search disagrees with direct factorization in degree ten")


def check(n, row, gp, trinomials, scalar_pairs=None):
    p, q = row["degree_primes"]
    a, b = (1 << p) - 1, (1 << q) - 1
    if not (2 < p < q and p*q == n and all(fmpz(t).is_prime() for t in (p, q))):
        raise ValueError(f"incorrect degree factors at degree {n}")
    # On the rank-two side, 3*p^2/4 <= h <= n/3, and the subgroup contains x, 1+x.
    candidates = [h for h in range((3*p*p + 3)//4, n//3 + 1)
                  if a % h == 0 and contains_binary_plane(h)]
    records = {int(h): values for h, values in row.get("scalar_pair_counts", {}).items()}
    if set(records) != set(candidates):
        raise ValueError(f"missing or extraneous scalar orders in degree {n}")
    if scalar_pairs:
        for h in candidates:
            counts = scalar_counts(scalar_pairs, p, q, h)
            if counts != records[h] or counts[-1] != 0:
                raise ValueError(f"scalar pair census disagreement at degree {n}, order {h}")
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
        if not scalar_pairs and len(support) == 5 and any(sorted(Counter(e % h for e in support).values()) == [1, 2, 2]
                                     for h in candidates):
            raise ValueError(f"the scalar-order test is inconclusive for {support}")
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
    scope = "displayed supports" if candidates and not scalar_pairs else "all sparse irreducibles"
    print(f"Degree {n}: {len(str(large))}-digit prime verified, "
          f"forced for {scope}, primitive norms in degrees {p} and {q}, minimum weight {minimum}.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp")
    parser.add_argument("--trinomials", required=True, help="compiled scripts/prime_degree_trinomials.cpp")
    parser.add_argument("--scalar-pairs", help="compiled scripts/check_scalar_pairs.cpp for the all-support census")
    parser.add_argument("--degree", type=int, help="verify just one degree from the table")
    args = parser.parse_args()
    rows = json.loads((DATA / "semiprime-scalar-norms.json").read_text())
    if set(map(int, rows)) != {1727, 1781, 2353, 3817, 5053, 8033, 10967, 11581, 14263, 14971}:
        parser.error("incomplete semiprime norm records")
    if args.degree is not None and str(args.degree) not in rows:
        parser.error("degree is outside the table")
    if args.scalar_pairs:
        check_control(args.scalar_pairs)
    for n, row in rows.items():
        if args.degree is None or args.degree == int(n):
            check(int(n), row, args.gp, args.trinomials, args.scalar_pairs)
