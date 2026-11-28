"""Check the quadratic example and the three parameter sequences in degree 1229."""

import argparse
import csv
import gzip
import json
import subprocess
from collections import Counter
from pathlib import Path

from check_1229_norm_height import sparse_root
from check_1229_subgroup_traces import multiplication_table, multiply
from check_1229_wheel import EXTENDED_BOUND
from check_degree_1229 import COFACTOR, GROUP, KNOWN, N, PRIMES
from check_factor_base import DATA, irreducible, polynomial
from check_pair_products import reciprocal
from period_coordinate import mask_of
from period_fibres import minimal_polynomial


RADIUS = 4096


def check_degree_ten():
    field_mask = 0x46F
    field = polynomial(field_mask)
    if not irreducible(field):
        raise ArithmeticError("reducible example field")
    roots = (0x1E2, 0x3F6, 0x14B, 0x26E, 0x207)
    masks = (0x50B, 0x561, 0x4A9, 0x623, 0x50D)
    if len({min(f, reciprocal(f)) for f in masks}) != len(masks):
        raise ArithmeticError("repeated reciprocal class")
    projected = []
    for root, f, order in zip(roots, masks, (93, 93, 33, 33, 1023), strict=True):
        if minimal_polynomial(root, field_mask) != f or f.bit_length() != 11 or f.bit_count() != 5:
            raise ArithmeticError("incorrect degree-ten pentanomial")
        value = polynomial(root)
        if value.pow_mod(341, field) == 1 or value.pow_mod(order, field) != 1:
            raise ArithmeticError("known prime test or order multiple failed")
        for p in (3, 11, 31):
            if order % p == 0 and value.pow_mod(order // p, field) == 1:
                raise ArithmeticError("incorrect exact order")
        projected.append(value.pow_mod(3, field))
    curvature = polynomial(2).pow_mod(90, field)
    if (curvature.pow_mod(341, field) != 1 or
            any(curvature.pow_mod(341 // p, field) == 1 for p in (11, 31))):
        raise ArithmeticError("second difference does not generate the cofactor group")
    for left, middle, right in zip(projected, projected[1:], projected[2:]):
        if (left * right - curvature * middle**2) % field != 0:
            raise ArithmeticError("quadratic parameter identity failed")


def check_support_count():
    counts = Counter()
    previous = (0, 0, 0)
    with gzip.open(DATA / "degree-1229-irreducible-supports.csv.gz", "rt", newline="") as source:
        for row in csv.DictReader(source):
            a, b, c = taps = tuple(int(row[key]) for key in ("a", "b", "c"))
            if not (0 < a < b < c < N and previous < taps < (N - c, N - b, N - a)):
                raise ValueError("noncanonical or unordered sparse support")
            counts[int(row["missing_mask"])] += 1
            previous = taps
    if counts != {0: 319572, 1: 5, 2: 6} or (counts[0] - 1).bit_length() != 19:
        raise ArithmeticError(f"unexpected survivor counts {counts}")
    if (EXTENDED_BOUND + 1)**16 <= COFACTOR:
        raise ArithmeticError("the archived prime floor does not give the fifteen-prime bound")


def check_quadratic_known_tests(a, b, field):
    # The curvature has trivial projection at every prime dividing K.
    for p in PRIMES:
        first, second = (v.pow_mod(GROUP // p, field) for v in (a, b))
        ratio = second * first.pow_mod(p - 1, field) % field
        table = multiplication_table(mask_of(ratio), mask_of(field))
        value = mask_of(first * ratio.pow_mod((-RADIUS) % p, field) % field)
        for t in range(-RADIUS, RADIUS + 1):
            if value == 1:
                raise ArithmeticError(f"quadratic parameter {t} fails the test at {p}")
            value = multiply(value, table)


def check_degree_1229(executable):
    check_support_count()
    certificate = json.loads((DATA / "degree-1229-q1024-certificate.json").read_text())
    field = polynomial(int(certificate["modulus_hex"], 16))
    a, b = (sparse_root(name, field) for name in ("product", "seroussi"))
    check_quadratic_known_tests(a, b, field)
    inputs = (RADIUS, KNOWN, mask_of(field), mask_of(a), mask_of(b))
    result = subprocess.run([executable], input=" ".join(map(str, inputs)) + "\n",
                            text=True, stdout=subprocess.PIPE, check=True)
    expected = [
        "product hit 0 0 27 50 77 1229",
        "product minimum-above-five 555 -1939",
        "product distinct 8193",
        "seroussi hit 0 0 2 6 15 1229",
        "seroussi minimum-above-five 549 334",
        "seroussi distinct 8193",
        "quadratic hit 0 0 27 50 77 1229",
        "quadratic hit 1 0 2 6 15 1229",
        "quadratic minimum-above-five 545 -1545",
        "quadratic distinct 8193",
    ]
    if result.stdout.splitlines() != expected:
        raise ArithmeticError(f"unexpected weight census\n{result.stdout}")
    print(result.stdout, end="")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("census", type=Path, help="compiled census_1229_parameter_weights executable")
    args = parser.parse_args()
    check_degree_ten()
    print("Five degree-10 reciprocal classes have root orders 93, 93, 33, 33 and 1023.")
    check_degree_1229(args.census.resolve())
