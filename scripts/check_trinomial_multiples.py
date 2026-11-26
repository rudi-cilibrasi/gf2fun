"""Enumerate normalized five-term divisors of trinomials with a bounded-weight quotient."""

import argparse
import csv
import sys
from collections import defaultdict
from functools import lru_cache
from math import comb, gcd

from sympy import factorint

from check_factor_base import polynomial
from make_witnesses import exact_quotient, mask_product, primitive
from period_coordinate import mask_of


def degree_bounds(weight):
    edges = weight + 2
    return 2 * edges**3 // 27, comb(edges, 4)


def divisors(factors, limit, index=0, value=1):
    if index == len(factors):
        yield value
        return
    p, multiplicity = factors[index]
    degree = p.bit_length() - 1
    capacity = (limit - (value.bit_length() - 1)) // degree
    for power in range(min(multiplicity, capacity) + 1):
        if power:
            value = mask_product(value, p)
        yield from divisors(factors, limit, index + 1, value)


def reverse(mask):
    return int(format(mask, "b")[::-1], 2)


def normalized(mask):
    return gcd(*(i for i in range(1, mask.bit_length()) if mask >> i & 1)) == 1


def find_products(max_weight):
    nmax, mmax = degree_bounds(max_weight)
    for degree in range(4, nmax + mmax + 1):
        for tap in range(1, degree // 2 + 1):
            parent = (1 << degree) | (1 << tap) | 1
            factors = [(mask_of(p), e) for p, e in polynomial(parent).factor()[1]]
            for f in divisors(factors, nmax):
                if f.bit_count() != 5 or not normalized(f):
                    continue
                g = exact_quotient(parent, f)
                weight = g.bit_count()
                if weight > max_weight:
                    continue
                n = f.bit_length() - 1
                nb, mb = degree_bounds(weight)
                if n > nb or degree - n > mb or mask_product(f, g) != parent:
                    raise ArithmeticError("product or degree bound failed")
                yield weight, degree, tap, f, g
                if 2*tap != degree:
                    yield weight, degree, degree - tap, reverse(f), reverse(g)


@lru_cache(maxsize=None)
def is_primitive(mask):
    n = mask.bit_length() - 1
    return primitive(n, mask, factorint((1 << n) - 1))


def summarize(rows):
    polynomials = {f for _, _, _, f, _ in rows}
    generators = {f for f in polynomials if is_primitive(f)}
    return (len(rows), len(polynomials), max(f.bit_length()-1 for f in polynomials),
            len(generators), max(f.bit_length()-1 for f in generators))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, choices=(3, 5, 7, 9), default=7)
    parser.add_argument("--list", action="store_true", help="print both supports for every product")
    args = parser.parse_args()
    results = defaultdict(list)
    for row in find_products(args.through):
        results[row[0]].append(row)
    expected = {3: (17, 15, 7, 8, 7), 5: (36, 32, 11, 10, 8),
                7: (67, 57, 13, 30, 13), 9: (77, 69, 18, 26, 17)}
    out = csv.writer(sys.stdout, lineterminator="\n")
    if args.list:
        out.writerow(("quotient_weight", "parent_degree", "parent_tap", "factor_degree", "a", "b", "c"))
    else:
        out.writerow(("quotient_weight", "products", "pentanomials", "maximum_degree",
                      "primitive_pentanomials", "maximum_primitive_degree"))
    for weight in range(3, args.through + 1, 2):
        rows = results[weight]
        counts = summarize(rows)
        if len(rows) != len(set(rows)) or counts != expected[weight]:
            raise ArithmeticError(f"unexpected census at quotient weight {weight}: {counts}")
        if args.list:
            supports = []
            for h, degree, tap, f, _ in rows:
                n = f.bit_length()-1
                interior = [i for i in range(1, n) if f >> i & 1]
                supports.append((h, degree, tap, n, *interior))
            out.writerows(sorted(supports))
        else:
            out.writerow((weight, *counts))
