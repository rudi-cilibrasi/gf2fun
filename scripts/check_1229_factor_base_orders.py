"""Replay the exact orders and minimum term count in the degree-1229 projected-log table."""

import argparse
import csv
import gzip
import hashlib
import json
import subprocess
from collections import Counter
from math import gcd
from pathlib import Path

from check_1229_frobenius_models import power_basis_expression
from check_degree_1229 import COFACTOR, GROUP, PRIMES, check_known_order
from check_factor_base import DATA, irreducible, polynomial
from period_coordinate import mask_of


METADATA = DATA / "degree-1229-q1024-certificate.json"
LOGS = DATA / "degree-1229-q1024-projected-logs.csv.gz"
EXPECTED_DEGREES = {1: 2, 2: 1, 4: 3, 5: 6, 10: 99, 20: 52377}
LIGHTEST = {0x11C4B7, 0x193377}
EXCEPTION = 0x16FEC7


def read_table():
    cert = json.loads(METADATA.read_text())
    if hashlib.sha256(LOGS.read_bytes()).hexdigest() != cert["csv_gz_sha256"]:
        raise ValueError("projected-log table digest mismatch")
    with gzip.open(LOGS, "rt", newline="") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != ["mask", "exponent"]:
            raise ValueError("unexpected projected-log columns")
        entries = [(int(row["mask"]), int(row["exponent"])) for row in reader]
    logs = dict(entries)
    if (len(logs) != len(entries) or Counter(m.bit_length()-1 for m in logs) != EXPECTED_DEGREES
            or logs.get(2) != 1 or any(not 0 <= e < COFACTOR or gcd(e, COFACTOR) != 1 for e in logs.values())):
        raise ValueError("invalid projected-log table")
    return int(cert["modulus_hex"], 16), logs


def check_examples(modulus_mask, logs):
    from check_degree_1229 import KNOWN
    field = polynomial(modulus_mask)
    x = polynomial(2)
    if not irreducible(field) or field.degree() != 1229:
        raise ValueError("invalid model field")
    check_known_order(field)
    for mask in sorted(LIGHTEST | {EXCEPTION}):
        value = polynomial(mask)
        if not irreducible(value) or x.pow_mod(KNOWN, field).pow_mod(logs[mask], field) != value.pow_mod(KNOWN, field):
            raise ArithmeticError(f"invalid projected logarithm at {mask:#x}")
        missing = [p for p in PRIMES if value.pow_mod(GROUP//p, field) == 1]
        if missing != ([46703] if mask == EXCEPTION else []):
            raise ArithmeticError(f"unexpected prime projections at {mask:#x}")
        # Expand value^1229 in 1, value, ..., value^1228. The result is unique.
        leading_power = mask_of(value.pow_mod(1229, field))
        relation = power_basis_expression(mask, leading_power, modulus_mask) + x**1229
        if relation.compose_mod(value, field) != 0 or mask_of(relation).bit_count() != (653 if mask == EXCEPTION else 545):
            raise ArithmeticError(f"incorrect minimal polynomial at {mask:#x}")


def census(executable, modulus_mask, logs):
    header = " ".join(map(str, (modulus_mask, *PRIMES)))
    source = "\n".join([header, *(f"{m} {e}" for m, e in logs.items())]) + "\n"
    proc = subprocess.run([str(executable.resolve())], input=source, text=True,
                          stdout=subprocess.PIPE, check=True)
    rows = [tuple(map(int, line.split())) for line in proc.stdout.splitlines()]
    if [m for m, _, _ in rows] != list(logs):
        raise ArithmeticError("incomplete census")
    if [(m, flags) for m, _, flags in rows if flags] != [(EXCEPTION, 2)]:
        raise ArithmeticError("unexpected known-prime order tests")
    least = min(w for _, w, _ in rows)
    if least != 545 or {m for m, w, _ in rows if w == least} != LIGHTEST:
        raise ArithmeticError("unexpected minimum term count")
    print(f"All {len(rows):,} projected identities checked. Exactly {len(rows)-1:,} elements have full order.")
    print("The one exception has index 46,703. The minimum weight is 545 at masks 0x11c4b7 and 0x193377.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", type=Path, metavar="NTL_EXECUTABLE",
                        help="check all 52,488 rows with the compiled census_1229_factor_base.cpp")
    args = parser.parse_args()
    modulus_mask, logs = read_table()
    check_examples(modulus_mask, logs)
    print("Checked both 545-term examples and the exceptional 653-term example directly with FLINT.")
    if args.census:
        census(args.census, modulus_mask, logs)
