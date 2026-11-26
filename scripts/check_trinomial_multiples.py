"""Enumerate normalized five-term divisors of trinomials with a bounded-weight quotient."""

import argparse
import csv
import sys
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache, partial
from math import comb, gcd, prod

from sympy import factorint

from check_factor_base import polynomial
from make_witnesses import exact_quotient, mask_product, primitive, remainder
from period_coordinate import mask_of


def degree_bounds(weight):
    edges = weight + 2
    return 2 * edges**3 // 27, comb(edges, 4)


def divisors(factors, limit, index=0, value=1, stop_degree=None):
    if index == len(factors) or (stop_degree is not None and value.bit_length()-1 >= stop_degree):
        yield value
        return
    p, multiplicity = factors[index]
    degree = p.bit_length() - 1
    capacity = (limit - (value.bit_length() - 1)) // degree
    for power in range(min(multiplicity, capacity) + 1):
        if power:
            value = mask_product(value, p)
        yield from divisors(factors, limit, index + 1, value, stop_degree)


@lru_cache(maxsize=512)
def sparse_multiples(divisor, limit):
    """Find 1 + X^a + X^b + X^c + X^d divisible by divisor, with a < b < c < d."""
    powers = [1]
    for _ in range(limit):
        powers.append(remainder(powers[-1] << 1, divisor))
    pairs = defaultdict(list)
    multiples = []
    for c in range(3, limit):
        b = c-1
        for a in range(1, b):
            pairs[powers[a] ^ powers[b]].append((1 << a) | (1 << b))
        for d in range(c+1, limit+1):
            high = (1 << c) | (1 << d) | 1
            for low in pairs.get(1 ^ powers[c] ^ powers[d], ()):
                multiples.append(high | low)
    return tuple(multiples)


def five_term_divisors(factors, parent, limit):
    if prod(e+1 for _, e in factors) <= 32768:
        yield from (f for f in divisors(factors, limit) if f.bit_count() == 5)
        return
    # A divisor with degree at least 14 contains one of the prefix products.
    # Complete its four positive exponents by matching two pairs of residues.
    candidates = set()
    for prefix in divisors(factors, limit, stop_degree=14):
        if prefix.bit_length()-1 < 14:
            if prefix.bit_count() == 5:
                candidates.add(prefix)
        else:
            candidates.update(sparse_multiples(prefix, limit))
    yield from (f for f in candidates if remainder(parent, f) == 0)


def reverse(mask):
    return int(format(mask, "b")[::-1], 2)


def normalized(mask):
    return gcd(*(i for i in range(1, mask.bit_length()) if mask >> i & 1)) == 1


def products_for_degree(degree, max_weight):
    nmax, _ = degree_bounds(max_weight)
    rows = []
    for tap in range(1, degree // 2 + 1):
        parent = (1 << degree) | (1 << tap) | 1
        factors = [(mask_of(p), e) for p, e in polynomial(parent).factor()[1]]
        for f in five_term_divisors(factors, parent, nmax):
            if not normalized(f):
                continue
            g = exact_quotient(parent, f)
            weight = g.bit_count()
            if weight > max_weight:
                continue
            n = f.bit_length() - 1
            nb, mb = degree_bounds(weight)
            if n > nb or degree - n > mb or mask_product(f, g) != parent:
                raise ArithmeticError("product or degree bound failed")
            rows.append((weight, degree, tap, f, g))
            if 2*tap != degree:
                rows.append((weight, degree, degree - tap, reverse(f), reverse(g)))
    return rows


def find_products(max_weight, jobs=1):
    nmax, mmax = degree_bounds(max_weight)
    degrees = range(4, nmax + mmax + 1)
    search = partial(products_for_degree, max_weight=max_weight)
    if jobs == 1:
        for degree in degrees:
            yield from search(degree)
    else:
        with ProcessPoolExecutor(max_workers=jobs) as pool:
            for rows in pool.map(search, degrees):
                yield from rows


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
    parser.add_argument("--jobs", type=int, default=1, help="parallel parent degrees")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    results = defaultdict(list)
    for row in find_products(args.through, args.jobs):
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
