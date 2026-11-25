"""Check the normal basis generator obtained from successive subspaces of an Ore root."""

import argparse
import json
from itertools import combinations
from math import comb

from flint import nmod_poly
from sympy import divisors

from check_ore_lifts import lifted_support
from check_ore_norms import first_relation, from_support, prefix_products, support
from make_witnesses import primitive, remainder, table_factors


def check_basis(seed):
    s = seed[-1]
    n = (1 << s) - 1
    modulus = from_support(lifted_support(seed))
    basis = [from_support([1 << i]) for i in range(s)]
    generator = nmod_poly([], 2)
    for b, value in enumerate(prefix_products(basis, modulus), start=1):
        rank = comb(s, b)
        relation = first_relation(value, modulus, rank, frobenius=True)
        if relation.bit_length() != rank + 1:
            raise ArithmeticError(f"incorrect rank in dimension {b} for {seed}")
        generator += value
    relation = first_relation(generator, modulus, n, frobenius=True)
    if relation != ((1 << n) | 1):
        raise ArithmeticError(f"the conjugates do not form a normal basis for {seed}")


def echelon_bases(s, b):
    """Enumerate each b-plane once by its reduced row echelon basis."""
    for pivots in combinations(range(s), b):
        free = [(i, j) for i, p in enumerate(pivots) for j in range(p + 1, s) if j not in pivots]
        for bits in range(1 << len(free)):
            rows = [1 << p for p in pivots]
            for k in support(bits):
                i, j = free[k]
                rows[i] |= 1 << j
            yield rows


def check_all_subspaces(seed):
    s = seed[-1]
    n = (1 << s) - 1
    seed_mask = sum(1 << i for i in seed)
    modulus = from_support(lifted_support(seed))
    logs = {}
    point = 1
    for k in range(n):
        logs[point] = k
        point = remainder(point << 1, seed_mask)
    periods = divisors(n)
    seen = set()
    for b in range(1, s + 1):
        for rows in echelon_bases(s, b):
            basis = [from_support([1 << i for i in support(row)]) for row in rows]
            value = list(prefix_products(basis, modulus))[-1]
            key = bytes(map(int, value.coeffs()))
            if key in seen:
                raise ArithmeticError(f"two subspaces have the same product for {seed}")
            seen.add(key)
            points = [0]
            for row in rows:
                points += [x ^ row for x in points]
            exponents = {logs[x] for x in points if x}
            orbit_size = next(d for d in periods if all((e + d) % n in exponents for e in exponents))
            field_degree = next(d for d in periods if value.pow_mod(1 << d, modulus) == value)
            if field_degree != orbit_size:
                raise ArithmeticError(f"incorrect subspace product degree for {seed}, basis {rows}")
    return len(seen)


def survey(s, table, all_subspaces):
    if s < 2:
        raise ValueError("expected a seed degree of at least two")
    factors = table_factors(s, table)
    count = 0
    subspaces = 0
    for terms in (1, 3):
        for interior in combinations(range(1, s), terms):
            seed = (0, *interior, s)
            if primitive(s, sum(1 << i for i in seed), factors):
                check_basis(seed)
                if all_subspaces:
                    subspaces += check_all_subspaces(seed)
                count += 1
    print(f"verified flag products and normal generators for {count} seeds of degree {s}"
          f" in the field of degree {(1 << s) - 1}")
    if all_subspaces:
        print(f"verified distinct products and exact field degrees for {subspaces} seed/subspace pairs")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("seed_degree", type=int)
    parser.add_argument("--factor-table", required=True, type=argparse.FileType("r"))
    parser.add_argument("--all-subspaces", action="store_true", help="also exhaust all nonzero seed subspaces")
    args = parser.parse_args()
    with args.factor_table as source:
        data = json.load(source)
    survey(args.seed_degree, data.get("table2-_data", data), args.all_subspaces)
