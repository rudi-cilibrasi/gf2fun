"""Check partial order certificates for the five open degrees just above 1229."""

import json
from math import gcd, prod
from pathlib import Path

from flint import fmpz, fmpz_mod_poly_ctx

from batch_degree_1229 import block_product


DATA = Path(__file__).resolve().parents[1] / "data" / "open-degrees-1231-1259.json"


def check(row):
    n, u, v = row["degree"], row["u"], row["v"]
    primes, cofactor = row["known_prime_factors"], row["cofactor"]
    known, order = prod(primes), (1 << n) - 1
    if (not 0 < u < v < u+v < n or cofactor <= 1 or known*cofactor != order
            or gcd(known, cofactor) != 1 or not all(fmpz(p).is_prime() for p in primes)):
        raise ValueError(f"incorrect support or group-order data in degree {n}")

    x = fmpz_mod_poly_ctx(2).gen()
    f = x**n + (x**u + 1)*(x**v + 1)
    if not f.is_irreducible() or x.pow_mod(order, f) != 1:
        raise ValueError(f"field or full-power check failed in degree {n}")
    if any(x.pow_mod(order//p, f) == 1 for p in set(primes)) or x.pow_mod(known, f) == 1:
        raise ValueError(f"partial root-order check failed in degree {n}")

    # Every cofactor prime has ord_q(2) = n, hence q = 1 mod 2n for odd n.
    if n % 2 == 0 or any(gcd((1 << (n//int(p))) - 1, cofactor) != 1 for p, _ in fmpz(n).factor()):
        raise ValueError(f"the cofactor contains a smaller-degree prime in degree {n}")
    k = row["log_block"]
    product = block_product(cofactor, 2*n, k, method="lagrange")
    if product != row["progression_product"] or gcd(product, cofactor) != 1:
        raise ValueError(f"the divisor progression failed in degree {n}")
    bound = 1 + 2*n*(1 << (2*k))
    print(f"{n}: taps {u}, {v}, {u+v}. Every cofactor prime exceeds {bound}. "
          f"Root order exceeds 2^{(known*bound).bit_length()-1}.")


if __name__ == "__main__":
    rows = json.loads(DATA.read_text())
    if [row["degree"] for row in rows] != [1231, 1237, 1243, 1249, 1259]:
        raise ValueError("incomplete open-degree table")
    for row in rows:
        check(row)
