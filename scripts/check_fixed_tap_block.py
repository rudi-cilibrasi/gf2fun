"""Check primitive factors of every retained tap pair at two consecutive degrees."""

import csv
from collections import Counter
from math import gcd
from pathlib import Path

from flint import fmpz, nmod_poly

from check_fixed_tap_cover import (
    EVEN_TAPS, ODD_TAPS, PERIOD, X, certified_classes, root_order, small_fields,
)


def main():
    fields = small_fields()
    residue, modulus = 1229, PERIOD
    expected = set()
    for j, menu in enumerate((ODD_TAPS, EVEN_TAPS)):
        for u, v in menu:
            classes = certified_classes(u, v, j == 0, fields, False)
            if (classes >> (residue + j)) & 1:
                expected.add((j, u, v))

    path = Path(__file__).resolve().parents[1] / "data/fixed-tap-primitive-factors.csv"
    counts = Counter()
    certificates = []
    degrees = set()
    with path.open() as source:
        for row in csv.DictReader(source):
            j, u, v, p, e = (int(row[key]) for key in ("offset", "u", "v", "degree", "exponent"))
            mask = int(row["factor_mask"], 16)
            factor = nmod_poly([(mask >> i) & 1 for i in range(mask.bit_length())], 2)
            group_order = 2**p - 1
            if p in degrees or p <= 6 or not fmpz(p).is_prime():
                raise ValueError(f"invalid factor degree {p}")
            if factor.degree() != p or factor.factor()[1] != [(factor, 1)]:
                raise ValueError(f"invalid irreducible factor {factor}")
            if root_order(factor) != group_order:
                raise ValueError(f"factor of degree {p} has deficient order")
            tail = (1+X**u)*(1+X**v)
            if (X.pow_mod(e, factor) + tail) % factor != 0:
                raise ValueError(f"incorrect exponent at {(j, u, v, p)}")
            if gcd(group_order, modulus) != 1 or gcd(e-j, group_order) != 1:
                raise ValueError("congruences do not give a reduced class")
            residue += modulus * (((e-j-residue)*pow(modulus, -1, group_order)) % group_order)
            modulus *= group_order
            counts[j, u, v] += 1
            degrees.add(p)
            certificates.append((j, factor, tail))

    if set(counts) != expected or any(count != 2 for count in counts.values()):
        raise ValueError("expected two factors for every retained tap pair")
    start = residue + 75*modulus
    if not fmpz(start).is_prime() or start % PERIOD != 1229:
        raise ArithmeticError("the specified block does not start at a prime in the selected class")
    for j, factor, tail in certificates:
        if (X.pow_mod(start+j, factor) + tail) % factor != 0:
            raise ArithmeticError("direct modular division at the prime start failed")
    print(f"{len(certificates)} primitive factors of distinct prime degrees from {min(degrees)} "
          f"through {max(degrees)} for {len(expected)} retained tap pairs.")
    print(f"Reduced progression: n = {residue} modulo {modulus}")
    print(f"Prime start: {start}")


if __name__ == "__main__":
    main()
