"""Check all surviving trinomials at degree 3927, their cubes, and one low-tap pentanomial."""

import argparse
import csv
import io
import json
import subprocess
from math import prod
from pathlib import Path

from flint import fmpz, nmod_poly

from check_product_range import prime_index_powers


DEGREE = 3927
GROUP = 2**DEGREE - 1
SMALL_ORDER = 7 * (2**561 - 1)
ORDERS = {
    367: GROUP,
    370: GROUP,
    497: SMALL_ORDER,
    763: SMALL_ORDER,
    898: GROUP,
    1085: SMALL_ORDER,
    1385: GROUP,
    1444: GROUP,
    1517: GROUP // 127,
    1520: GROUP // 7,
}
X = nmod_poly([0, 1], 2)


def order_factors():
    path = Path(__file__).resolve().parents[1] / "data" / "mersenne-symmetric-above-7560.json"
    larger = json.loads(path.read_text())["7854"]
    factors = [p for p in larger if GROUP % p == 0]
    if prod(factors) != GROUP or not all(fmpz(p).is_prime() for p in set(factors)):
        raise ValueError("incomplete prime factorization for degree 3927")
    return factors


def check_order(f, order, factors):
    if GROUP % order or X.pow_mod(order, f) != 1:
        raise ValueError("incorrect full power")
    primes = sorted(p for p in set(factors) if order % p == 0)
    if any(value == 1 for _, value in prime_index_powers(X, order, primes, f)):
        raise ValueError("a proper divisor gives the identity")


def check_census(program, factors):
    row = " ".join(map(str, [DEGREE, len(factors), *factors])) + "\n"
    run = subprocess.run([program], input=row, text=True, capture_output=True, check=True)
    [result] = csv.DictReader(io.StringIO(run.stdout))
    irreducible = [int(a) for a in result["irreducible_taps"].split()]
    primitive = [int(a) for a in result["primitive_taps"].split()]
    if (int(result["degree"]) != DEGREE or irreducible != list(ORDERS)
            or primitive != [a for a, order in ORDERS.items() if order == GROUP]):
        raise ValueError("trinomial census disagreement")
    print("NTL exhausted all 1,963 reciprocal classes.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ntl", help="compiled scripts/prime_degree_trinomials.cpp")
    args = parser.parse_args()
    factors = order_factors()
    if args.ntl:
        check_census(args.ntl, factors)
    for tap, order in ORDERS.items():
        f = X**DEGREE + X**tap + 1
        if (X.pow_mod(1 << DEGREE, f) != X
                or any((X.pow_mod(1 << (DEGREE // l), f) + X).gcd(f) != 1
                       for l in (3, 7, 11, 17))):
            raise ValueError(f"reducible trinomial at tap {tap}")
        check_order(f, order, factors)
        check_order((1 + X**1309)**3 + X**tap, order, factors)
    check_order(X**DEGREE + X**113 + X**101 + X**12 + 1, GROUP, factors)
    print(f"FLINT verified {len(set(factors))} primes, ten trinomial orders, and eleven pentanomial orders.")
    print("The primitive trinomial taps up to reciprocity are 367, 370, 898, 1385, and 1444.")


if __name__ == "__main__":
    main()
