"""Find binomial tails in the published product witnesses and check the degree-2574 example."""

import argparse
import csv
import json
from math import gcd, prod

from flint import fmpz
from check_factor_base import DATA, polynomial


def witnesses():
    rows = set()
    for path in sorted(DATA.glob("*product-witnesses*.csv")):
        with path.open(newline="") as stream:
            for row in csv.DictReader(stream):
                n, u, v = (int(row[key]) for key in ("degree", "u", "v"))
                if u.bit_count() != 1 or v.bit_count() != 1:
                    continue
                k = u+v
                order = 2**n-1
                if not 0 < u < v < k < n or gcd(n, k) != 1 or gcd(k, order) != 1:
                    raise ArithmeticError(f"invalid binomial-tail witness in degree {n}")
                rows.add((n, k, gcd(n, order)))
    return sorted(rows)


def check_2574():
    n, k = 2574, 5
    with (DATA / "mersenne-2561-2688.json").open() as stream:
        factors = json.load(stream)[str(n)]
    order = 2**n-1
    if prod(factors) != order or not all(fmpz(p).is_prime() for p in set(factors)):
        raise ArithmeticError("incorrect factorization of the degree-2574 group order")
    x = polynomial(2)
    tail, trinomial = x**n + (x+1)**k, x**n + x**k + 1
    if tail != x**n + x**5 + x**4 + x + 1 or tail.compose_mod(x**k, trinomial) != 0:
        raise ArithmeticError("the fifth power does not give the stated pentanomial root")
    for value, modulus, expected in ((x, trinomial, order), (x, tail, order), (x+1, tail, order//9)):
        if value.pow_mod(expected, modulus) != 1:
            raise ArithmeticError("the full order power failed")
        if any(value.pow_mod(expected//p, modulus) == 1 for p in set(factors) if expected % p == 0):
            raise ArithmeticError("a prime-index order power failed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="print each degree, tap and translate index")
    parser.add_argument("--powers", action="store_true", help="verify all three degree-2574 orders with FLINT")
    args = parser.parse_args()
    rows = witnesses()
    exceptions = {n: index for n, _, index in rows if index != 1}
    print(f"{len(rows)} archived product witnesses have two power-of-two taps.")
    print(f"Translate indices above one: {exceptions}")
    if args.list:
        for n, k, index in rows:
            print(n, k, index)
    if args.powers:
        if (2574, 5, 9) not in rows:
            raise ArithmeticError("the archived degree-2574 support or predicted index changed")
        check_2574()
        print("Verified both degree-2574 primitive polynomials and the exact index nine of the translate.")
