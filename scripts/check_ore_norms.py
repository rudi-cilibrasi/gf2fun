"""Check relative norms of roots of sparse primitive Ore lifts. Requires SymPy and python-flint."""

import argparse
import json
from collections import Counter
from itertools import combinations, product

from flint import nmod_poly

from check_ore_lifts import lifted_support, order_index
from make_witnesses import mask_product, primitive, remainder, table_factors, x_power


def from_support(support):
    coeffs = [0] * (max(support) + 1)
    for i in support:
        coeffs[i] = 1
    return nmod_poly(coeffs, 2)


def support(mask):
    return tuple(i for i in range(mask.bit_length()) if mask & (1 << i))


def prefix_products(basis, modulus):
    """Yield the product of the nonzero binary combinations of each successive prefix."""
    values = list(basis)
    result = nmod_poly([1], 2)
    for i, pivot in enumerate(values):
        result = result * pivot % modulus
        yield result
        for j in range(i + 1, len(values)):
            values[j] = values[j] * (values[j] + pivot) % modulus


def relative_norm(seed, s, b, modulus):
    """Compute the subspace product for the distinguished subfield of the seed field."""
    m = ((1 << s) - 1) // ((1 << b) - 1)
    scalar = x_power(m, seed)
    basis = []
    value = 1
    for _ in range(b):
        basis.append(from_support([1 << i for i in support(value)]))
        value = remainder(mask_product(value, scalar), seed)
    return list(prefix_products(basis, modulus))[-1]


def first_relation(value, modulus, bound, *, frobenius):
    """Return the first binary dependence of 1,v,v^2,... or of v,v^2,v^4,... ."""
    pivots = {}
    current = value if frobenius else nmod_poly([1], 2)
    for i in range(bound + 1):
        digits = bytes(map(int, current.coeffs()))
        row = int(digits[::-1].translate(BINARY_DIGITS), 2) if digits else 0
        relation = 1 << i
        while row:
            column = row.bit_length() - 1
            if column not in pivots:
                pivots[column] = row, relation
                break
            other, coefficients = pivots[column]
            row ^= other
            relation ^= coefficients
        else:
            return relation
        current = current * (current if frobenius else value) % modulus
    raise ArithmeticError("no dependence by the predicted field degree")


BINARY_DIGITS = bytes.maketrans(bytes([0, 1]), b"01")


def predicted_annihilator(seed, s, b):
    """Multiply the factors indexed by transversals of the residue classes modulo b."""
    polynomial = [1]
    classes = [range(j, s, b) for j in range(b)]
    for indices in product(*classes):
        exponent = sum(1 << i for i in indices)
        root = x_power(exponent, seed)
        scaled = [remainder(mask_product(c, root), seed) for c in polynomial]
        polynomial = [left ^ right for left, right in zip(scaled + [0], [0] + polynomial)]
    if any(c not in (0, 1) for c in polynomial):
        raise ArithmeticError("the predicted annihilator has a nonbinary coefficient")
    return sum(c << i for i, c in enumerate(polynomial))


def norm_profile(seed_support, b, factors, direct):
    seed = sum(1 << i for i in seed_support)
    s = seed_support[-1]
    n = (1 << s) - 1
    m = n // ((1 << b) - 1)
    modulus = from_support(lifted_support(seed_support))
    norm = relative_norm(seed, s, b, modulus)
    if direct:
        exponent = ((1 << n) - 1) // ((1 << m) - 1)
        if nmod_poly([0, 1], 2).pow_mod(exponent, modulus) != norm:
            raise ArithmeticError(f"direct norm disagrees for {seed_support}")
    minimum = first_relation(norm, modulus, m, frobenius=False)
    if minimum.bit_length() != m + 1:
        raise ArithmeticError(f"norm has smaller field degree for {seed_support}")
    annihilator = first_relation(norm, modulus, m, frobenius=True)
    if annihilator != predicted_annihilator(seed, s, b):
        raise ArithmeticError(f"incorrect Frobenius annihilator for {seed_support}")
    return minimum, order_index(support(minimum), factors)


def survey(s, b, table, direct):
    if b < 1 or s < 2 or b >= s or s % b:
        raise ValueError("the subfield degree must be a positive proper divisor of the seed degree")
    n = (1 << s) - 1
    m = n // ((1 << b) - 1)
    seed_factors = table_factors(s, table)
    norm_factors = table_factors(m, table)
    indices = Counter()
    for terms in (1, 3):
        for interior in combinations(range(1, s), terms):
            candidate = (0, *interior, s)
            if not primitive(s, sum(1 << i for i in candidate), seed_factors):
                continue
            minimum, index = norm_profile(candidate, b, norm_factors, direct)
            indices[index] += 1
            if index > 1:
                print(f"  seed {candidate}, norm polynomial {minimum:#x}, norm index {index}", flush=True)
    print(f"seed degree {s}, lift degree {n}, norm degree {m}, Frobenius rank {(s // b) ** b}")
    print(f"  seeds by norm index {dict(sorted(indices.items()))}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("seed_degree", type=int)
    parser.add_argument("subfield_degree", type=int, help="degree of the subfield in the seed field")
    parser.add_argument("--factor-table", required=True, type=argparse.FileType("r"))
    parser.add_argument("--direct", action="store_true", help="also check by powering in the lifted field")
    args = parser.parse_args()
    with args.factor_table as source:
        table = json.load(source)
    survey(args.seed_degree, args.subfield_degree, table.get("table2-_data", table), args.direct)
