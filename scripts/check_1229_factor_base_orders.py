"""Replay the exact orders and minimum term count in the degree-1229 projected-log table."""

import argparse
import csv
import gzip
import hashlib
import json
import subprocess
from collections import Counter
from math import gcd, prod
from pathlib import Path

from check_1229_frobenius_models import power_basis_expression
from check_degree_1229 import COFACTOR, GROUP, PRIMES, check_known_order
from check_factor_base import DATA, irreducible, polynomial
from period_coordinate import mask_of


METADATA = DATA / "degree-1229-q1024-certificate.json"
LOGS = DATA / "degree-1229-q1024-projected-logs.csv.gz"
ISOGENY_LOGS = DATA / "degree-1229-isogeny-logs.csv.gz"
CIRCLE_LOGS = DATA / "degree-1229-partial-circle-logs.csv"
EXTENDED_CENSUS = DATA / "degree-1229-extended-order-census.json"
EXPECTED_DEGREES = {1: 2, 2: 1, 4: 3, 5: 6, 10: 99, 20: 52377}
LIGHTEST = {0x11C4B7, 0x193377}
EXCEPTION = 0x16FEC7


def read_logs(path):
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", newline="") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != ["mask", "exponent"]:
            raise ValueError("expected mask,exponent columns")
        for row in reader:
            mask = row["mask"].strip()
            yield int(mask, 16 if mask.lower().startswith("0x") else 10), int(row["exponent"])


def read_table():
    cert = json.loads(METADATA.read_text())
    if hashlib.sha256(LOGS.read_bytes()).hexdigest() != cert["csv_gz_sha256"]:
        raise ValueError("projected-log table digest mismatch")
    entries = list(read_logs(LOGS))
    logs = dict(entries)
    if (len(logs) != len(entries) or Counter(m.bit_length()-1 for m in logs) != EXPECTED_DEGREES
            or logs.get(2) != 1 or any(not 0 <= e < COFACTOR or gcd(e, COFACTOR) != 1 for e in logs.values())):
        raise ValueError("invalid projected-log table")
    return int(cert["modulus_hex"], 16), logs


def extended_table(logs):
    result = dict(logs)
    for path in (ISOGENY_LOGS, CIRCLE_LOGS):
        for p, e in read_logs(path):
            if p in result or not 0 <= e < COFACTOR or gcd(e, COFACTOR) != 1:
                raise ValueError(f"invalid additional logarithm at {p:#x}")
            result[p] = e
    return result


def check_examples(modulus_mask, logs, examples=None):
    from check_degree_1229 import KNOWN
    if examples is None:
        examples = {p: (1, 545) for p in LIGHTEST} | {EXCEPTION: (46703, 653)}
    field = polynomial(modulus_mask)
    x = polynomial(2)
    if not irreducible(field) or field.degree() != 1229:
        raise ValueError("invalid model field")
    check_known_order(field)
    for mask, (index, terms) in examples.items():
        value = polynomial(mask)
        if not irreducible(value) or x.pow_mod(KNOWN, field).pow_mod(logs[mask], field) != value.pow_mod(KNOWN, field):
            raise ArithmeticError(f"invalid projected logarithm at {mask:#x}")
        missing = [p for p in PRIMES if value.pow_mod(GROUP//p, field) == 1]
        if prod(missing) != index:
            raise ArithmeticError(f"unexpected prime projections at {mask:#x}")
        # Expand value^1229 in 1, value, ..., value^1228. The result is unique.
        leading_power = mask_of(value.pow_mod(1229, field))
        relation = power_basis_expression(mask, leading_power, modulus_mask) + x**1229
        if relation.compose_mod(value, field) != 0 or mask_of(relation).bit_count() != terms:
            raise ArithmeticError(f"incorrect minimal polynomial at {mask:#x}")


def census(executable, modulus_mask, logs, extended=False):
    header = " ".join(map(str, (modulus_mask, *PRIMES)))
    source = "\n".join([header, *(f"{m} {e}" for m, e in logs.items())]) + "\n"
    command = [str(executable.resolve())]
    if extended:
        command.append("--extended")
    proc = subprocess.run(command, input=source, text=True,
                          stdout=subprocess.PIPE, check=True)
    rows = [tuple(map(int, line.split())) for line in proc.stdout.splitlines()]
    if [m for m, _, _ in rows] != list(logs):
        raise ArithmeticError("incomplete census")
    if extended:
        observed = summarize(rows)
        if observed != json.loads(EXTENDED_CENSUS.read_text()):
            raise ArithmeticError("the extended orders or weights differ from the published census")
        print(f"All {len(rows):,} projected identities checked. Exactly {observed['primitive']:,} elements "
              f"have full order. The minimum weight is {observed['minimum_weight']}.")
        return
    if [(m, flags) for m, _, flags in rows if flags] != [(EXCEPTION, 2)]:
        raise ArithmeticError("unexpected known-prime order tests")
    least = min(w for _, w, _ in rows)
    if least != 545 or {m for m, w, _ in rows if w == least} != LIGHTEST:
        raise ArithmeticError("unexpected minimum term count")
    print(f"All {len(rows):,} projected identities checked. Exactly {len(rows)-1:,} elements have full order.")
    print("The one exception has index 46,703. The minimum weight is 545 at masks 0x11c4b7 and 0x193377.")


def summarize(rows):
    least = min(w for _, w, _ in rows)
    ordered = sorted(rows)
    exceptions = [{"mask_hex": hex(p), "weight": w,
                   "index": prod(prime for i, prime in enumerate(PRIMES) if flags & (1 << i))}
                  for p, w, flags in ordered if flags]
    return {"elements": len(rows), "primitive": len(rows)-len(exceptions), "minimum_weight": least,
            "minimizers": [hex(p) for p, w, _ in ordered if w == least], "exceptions": exceptions}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", type=Path, metavar="NTL_EXECUTABLE",
                        help="check every order and term count with the compiled census_1229_factor_base.cpp")
    parser.add_argument("--extended", action="store_true", help="include the isogeny and circle logarithms")
    args = parser.parse_args()
    modulus_mask, logs = read_table()
    if args.extended:
        logs = extended_table(logs)
        summary = json.loads(EXTENDED_CENSUS.read_text())
        examples = {int(p, 16): (1, summary["minimum_weight"]) for p in summary["minimizers"]}
        examples.update({int(r["mask_hex"], 16): (r["index"], r["weight"]) for r in summary["exceptions"]})
        check_examples(modulus_mask, logs, examples)
        print("Checked every minimum-weight example and exceptional order in the extended census with FLINT.")
    else:
        check_examples(modulus_mask, logs)
        print("Checked both 545-term examples and the exceptional 653-term example directly with FLINT.")
    if args.census:
        census(args.census, modulus_mask, logs, args.extended)
