"""Census fifth and seventh powers of roots of irreducible degree-1229 pentanomials.

Run with uv run --no-project --with numpy --with python-flint==0.9.0 python
scripts/check_1229_power_images.py. The --task and --log options need only FLINT.
"""

import argparse
import json
from collections import Counter
from functools import cache
from math import gcd

from check_1229_frobenius_models import primitive_generator_in
from check_1229_sparse_frobenius import support_table
from check_degree_1229 import COFACTOR, GROUP, KNOWN, N, check_known_order
from check_factor_base import irreducible, modulus, polynomial
from period_coordinate import mask_of


SOURCE = (166, 249, 332)
TARGET = (332, 726, 1089)


@cache
def root_multipliers(m):
    """Multiplication by powers of a primitive m-th root in a small binary field."""
    field = {5: 0b11111, 7: 0b1011}[m]
    size = 1 << (field.bit_length()-1)
    rows = [list(range(size))]
    for _ in range(m):
        rows.append([(a << 1) ^ (field if (a << 1) >= size else 0) for a in rows[-1]])
    if rows[m] != rows[0] or len({row[1] for row in rows[:m]}) != m:
        raise ArithmeticError("invalid primitive root of unity")
    return rows[:m]


@cache
def norm_pattern(m, residues):
    """Monomial multiplicities with nonzero coefficients in the root-of-unity product."""
    multiples = root_multipliers(m)
    coefficients = {(0,)*len(residues): 1}
    for j in range(m):
        result = {}
        for counts, coefficient in coefficients.items():
            for i, exponent in enumerate(residues):
                next_counts = counts[:i] + (counts[i]+1,) + counts[i+1:]
                term = multiples[j*exponent % m][coefficient]
                result[next_counts] = result.get(next_counts, 0) ^ term
        coefficients = {k: v for k, v in result.items() if v}
    if any(c != 1 or sum(k*e for k, e in zip(counts, residues)) % m
           for counts, c in coefficients.items()):
        raise ArithmeticError("the norm failed descent to the base field")
    return tuple(coefficients)


def census(m, taps):
    import numpy as np
    if gcd(m, GROUP) != 1:
        raise ArithmeticError("powering could shorten the Frobenius orbit")
    a, b, c = taps
    tags = ((a % m)*m + b % m)*m + c % m
    ordering = np.argsort(tags, kind="stable")
    groups = np.split(ordering, np.flatnonzero(np.diff(tags[ordering])) + 1)
    counts = Counter()
    minimum, witnesses = N+1, []
    for indices in groups:
        supports = np.column_stack((np.zeros_like(indices), taps[:, indices].T,
                                    np.full_like(indices, N))).astype(np.int32)
        residues = supports[0] % m
        perm = np.argsort(residues, kind="stable")
        pattern = np.array(norm_pattern(m, tuple(map(int, residues[perm]))), dtype=np.int32)
        exponents = (supports[:, perm] @ pattern.T) // m
        parity = np.zeros((len(indices), N+1), dtype=np.uint8)
        np.bitwise_xor.at(parity, (np.arange(len(indices))[:, None], exponents), 1)
        weights = np.count_nonzero(parity, axis=1)
        for w, count in zip(*np.unique(weights, return_counts=True)):
            counts[int(w)] += 2*int(count)
        small = int(weights.min())
        if small < minimum:
            minimum, witnesses = small, []
        if small == minimum:
            for i in np.flatnonzero(weights == small):
                witnesses.append((tuple(map(int, supports[i, 1:4])),
                                  tuple(map(int, np.flatnonzero(parity[i])))))
    if sum(counts.values()) != 639166 or counts[minimum] != 2*len(witnesses):
        raise ArithmeticError("incomplete census")
    # Check each extremal image again by direct composition in the source field.
    x = polynomial(2)
    for taps, powers in witnesses:
        f = modulus(N, taps)
        g = polynomial(sum(1 << e for e in powers))
        if g.degree() != N or g.compose_mod(x**m, f) != 0:
            raise ArithmeticError("an extremal image fails direct substitution")
    return minimum, sorted(witnesses), counts


def verify_pair():
    x = polynomial(2)
    f, g = modulus(N, SOURCE), modulus(N, TARGET)
    if not irreducible(f) or not irreducible(g) or g.compose_mod(x**7, f) != 0:
        raise ArithmeticError("the seventh-power map fails")
    if x.pow_mod(7*pow(7, -1, GROUP), f) != x:
        raise ArithmeticError("seventh powering did not invert")
    for h in (f, g):
        check_known_order(h)
    return f


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    options = parser.add_mutually_exclusive_group()
    options.add_argument("--task", action="store_true", help="export the common-index logarithm task")
    options.add_argument("--log", type=int, metavar="EXPONENT", help="verify the common-index logarithm")
    args = parser.parse_args()
    f = verify_pair()
    if args.task or args.log is not None:
        base = primitive_generator_in(f).pow_mod(KNOWN, f)
        target = polynomial(2).pow_mod(KNOWN, f)
        if args.task:
            print(json.dumps({"source_taps": SOURCE, "seventh_power_taps": TARGET,
                              "field_modulus_hex": hex(mask_of(f)), "K": str(KNOWN), "C": str(COFACTOR),
                              "base_hex": hex(mask_of(base)), "target_hex": hex(mask_of(target))}, indent=2))
        else:
            if not 0 <= args.log < COFACTOR or base.pow_mod(args.log, f) != target:
                raise ValueError("the submitted logarithm fails direct powering")
            print(f"All four pentanomials have exact root index {gcd(args.log, COFACTOR)}.")
        return

    taps = support_table()
    for m, expected, count in ((5, 9, 14), (7, 5, 2)):
        minimum, witnesses, counts = census(m, taps)
        if (minimum, counts[minimum]) != (expected, count):
            raise ArithmeticError("unexpected minimum weight or multiplicity")
        if m == 7 and witnesses != [(SOURCE, (0, *TARGET, N))]:
            raise ArithmeticError("unexpected seventh-power pair")
        print(f"Power {m} across {sum(counts.values())} polynomials: "
              f"minimum weight {minimum}, attained by {count} sources including reciprocals.")


if __name__ == "__main__":
    main()
