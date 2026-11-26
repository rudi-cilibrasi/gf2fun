"""Find binomial tails in the published product witnesses and check the degree-2574 example."""

import argparse
import csv
import json
from math import gcd, prod
from pathlib import Path

from flint import fmpz
from check_factor_base import DATA, polynomial


def witnesses():
    rows = set()
    for path in sorted(DATA.glob("*product-witnesses*.csv")):
        with path.open(newline="") as stream:
            for row in csv.DictReader(stream):
                n, u, v = (int(row[key]) for key in ("degree", "u", "v"))
                if v % u or (v//u).bit_count() != 1:
                    continue
                k = 1+v//u
                order = 2**n-1
                if not 0 < u < v < u+v < n or gcd(n, k) != 1 or gcd(k, order) != 1:
                    raise ArithmeticError(f"invalid binomial-tail witness in degree {n}")
                rows.add((n, u, u+v, gcd(n, order)))
    return sorted(rows)


def factors_1229():
    from make_witnesses import remainder
    from period_coordinate import mask_of
    from period_fibres import minimal_polynomial

    n = 1229
    sources = {}
    with (DATA / "degree-1229-trinomial-factors.csv").open(newline="") as stream:
        for row in csv.DictReader(stream):
            tap, factor = int(row["tap"]), int(row["factor_mask"])
            sources[tap] = factor
            sources[n-tap] = int(f"{factor:b}"[::-1], 2)
    x = polynomial(2)
    for s in range(1, n.bit_length()):
        k = 1+2**s
        for u in range(1, (n-1)//k+1):
            v = u*(k-1)
            source = sources[u+v]
            if remainder((1 << n) | (1 << (u+v)) | 1, source):
                raise ArithmeticError("the supplied factor does not divide the source trinomial")
            element = mask_of(x.pow_mod(k, polynomial(source)))
            factor = minimal_polynomial(element, source)
            target = (1 << n) | (1 << (u+v)) | (1 << v) | (1 << u) | 1
            if not 0 < factor.bit_length()-1 < n or remainder(target, factor):
                raise ArithmeticError(f"failed to transport the proper factor at taps {u}, {v}")
            yield u, v, factor


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
    parser.add_argument("--list", action="store_true", help="print degree, smaller tap, trinomial tap and index of 1+r^u")
    parser.add_argument("--factors-1229", type=Path, metavar="CSV", help="derive, verify and write the 933 proper factors")
    parser.add_argument("--powers", action="store_true", help="verify all three degree-2574 orders with FLINT")
    args = parser.parse_args()
    rows = witnesses()
    exceptions = {n: index for n, _, _, index in rows if index != 1}
    print(f"{len(rows)} archived product witnesses have a power-of-two tap ratio.")
    print(f"Indices above one for 1+r^u: {exceptions}")
    if args.list:
        for row in rows:
            print(*row)
    if args.factors_1229:
        factors = list(factors_1229())
        if len(factors) != 933:
            raise ArithmeticError("incomplete degree-1229 enumeration")
        with args.factors_1229.open("w", newline="") as stream:
            writer = csv.writer(stream, lineterminator="\n")
            writer.writerow(("u", "v", "factor_mask"))
            writer.writerows(factors)
        degrees = [p.bit_length()-1 for _, _, p in factors]
        print(f"Verified {len(factors)} proper factors in degree 1229, of degrees {min(degrees)} through {max(degrees)}.")
    if args.powers:
        if (2574, 1, 5, 9) not in rows:
            raise ArithmeticError("the archived degree-2574 support or predicted index changed")
        check_2574()
        print("Verified both degree-2574 primitive polynomials and the exact index nine of the translate.")
