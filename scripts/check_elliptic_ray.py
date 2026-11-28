"""Verify elliptic-curve targets and order certificates in degrees 53 and 1229."""

import argparse
import csv
import gzip
import json
import subprocess
from fractions import Fraction
from math import gcd
from pathlib import Path

from check_1229_wheel import EXTENDED_BOUND, verify_extension
from check_degree_1229 import COFACTOR, KNOWN, check_known_order
from check_factor_base import DATA, irreducible, modulus, polynomial
from elliptic_ray_bound import quadratic_bound
from period_coordinate import CANDIDATES, coordinate, mask_of, period_polynomial


POINTS = DATA / "elliptic-ray-points.json"
TARGETS = DATA / "degree-1229-elliptic-targets.csv"
UNCONDITIONAL_TARGETS = DATA / "degree-1229-elliptic-unconditional-targets.csv.gz"
EXAMPLE = DATA / "degree-53-elliptic-logs.csv"
GP_SOURCE = Path(__file__).with_name("elliptic_ray_targets.gp")
TAPS53 = (2, 21, 23)
WEIGHTS1229 = (3, 9, 9, 14, 10, 12, 6, 4)
WEIGHTS53 = (10, 28, 20, 15)


def point_score(n, d, cosets, index_floor, weights):
    """Fejér bound for a cover with n*cosets split rational places, for odd d."""
    if d % 2 != 1 or index_floor < 2 or not weights or min(weights) < 0:
        raise ValueError("invalid elliptic moment parameters")
    norm = sum(Fraction(w*w, 1 << (i % 2)) for i, w in enumerate(weights))
    score = Fraction()
    for k in range(1, len(weights)):
        cross = sum(Fraction(w * weights[i+k], 1 << ((d*k + i%2 + (i+k)%2)//2))
                    for i, w in enumerate(weights[:-k]))
        score += 2*cross*(n*cosets - Fraction((1 << (d*k))+1, index_floor))
    return score/norm


def reconstruct(model, field_mask, rows, gp):
    n, d = model["degree"], model["constant_degree"]
    xs, ys = ([int(c, 16) for c in model[key]] for key in ("point_x_hex", "point_y_hex"))
    points = [model["generator"], model["translation"]]
    if (len(xs) != d or len(ys) != d or any(c < 0 or c.bit_length() > n for c in xs + ys)
            or any(len(p) != 2 or any(c < 0 or c.bit_length() > d for c in p) for p in points)
            or gcd(model["curve_order"] * ((1 << d)-1), (1 << n)-1) != 1):
        raise ValueError("invalid coordinates or noninvertible curve and constant orders")
    params = {"n": n, "d": d, "rows": rows, "card": model["curve_order"],
              "cmask": int(model["constant_modulus_hex"], 16), "emask": field_mask,
              "curvea": model.get("curve_a2", 1), "curveb": model["curve_b"],
              "generator": points[0], "translation": points[1],
              "xs": xs, "ys": ys}
    program = "".join(f"{key}={value};\n" for key, value in params.items()) + GP_SOURCE.read_text()
    proc = subprocess.run([gp, "-fq", "-s", "768M"], input=program, text=True,
                          capture_output=True, check=True)
    if proc.stderr:
        raise ArithmeticError(proc.stderr)
    table = [tuple(map(int, row)) for row in csv.reader(proc.stdout.splitlines())]
    if len(table) != rows or any(i != j or not 0 < x < 1 << n for j, (i, x) in enumerate(table)):
        raise ArithmeticError("incomplete or invalid elliptic targets")
    return [v for _, v in table]


def read_logs(paths):
    logs = {}
    for path in paths:
        with path.open(newline="") as stream:
            rows = csv.DictReader(stream)
            if rows.fieldnames != ["target", "exponent"]:
                raise ValueError(f"expected target,exponent in {path}")
            for row in rows:
                if None in row:
                    raise ValueError(f"unexpected columns in {path}")
                i, e = int(row["target"]), int(row["exponent"])
                if i in logs and logs[i] != e:
                    raise ValueError(f"conflicting exponents for target {i}")
                logs[i] = e
    return logs


def verify_logs(values, logs, f, basis, projection, group_order):
    base = polynomial(2).pow_mod(projection, f)
    for i, e in logs.items():
        if not 0 <= i < len(values) or not 0 <= e < group_order:
            raise ValueError(f"out-of-range target or exponent at {i}")
        target = polynomial(values[i])
        if basis is not None:
            target = target.compose_mod(basis, f)
        if base.pow_mod(e, f) != target.pow_mod(projection, f):
            raise ArithmeticError(f"incorrect logarithm for target {i}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, choices=(53, 1229), default=1229)
    parser.add_argument("--gp", default="gp")
    parser.add_argument("--logs", type=Path, nargs="+", help="CSV files with target,exponent")
    candidate = parser.add_mutually_exclusive_group()
    candidate.add_argument("--candidate", choices=CANDIDATES)
    candidate.add_argument("--taps", nargs=3, type=int, metavar=("A", "B", "C"))
    parser.add_argument("--projected", action="store_true",
                        help="verify powers in the degree-1229 cofactor subgroup")
    parser.add_argument("--no-order-tests", action="store_true",
                        help="use the 733 full-group targets in degree 1229, with no preliminary order tests")
    args = parser.parse_args()
    n = args.degree
    chosen = args.candidate or args.taps
    if n == 53 and (chosen or args.projected or args.no_order_tests):
        parser.error("degree 53 uses the published sparse root")
    if n == 1229 and (bool(args.logs) != bool(chosen) or (args.projected and not args.logs)):
        parser.error("a degree-1229 submission requires --logs and a candidate")
    if args.taps and not 0 < args.taps[0] < args.taps[1] < args.taps[2] < n:
        parser.error("expected three increasing interior exponents")
    if args.projected and args.no_order_tests:
        parser.error("the 733-target certificate uses full-group logarithms")
    d = 11 if n == 53 else (20 if args.no_order_tests else 19)
    model, = (m for m in json.loads(POINTS.read_text()) if (m["degree"], m["constant_degree"]) == (n, d))
    field = modulus(n, TAPS53) if n == 53 else period_polynomial(n)
    rows = 38 if n == 53 else (733 if args.no_order_tests else 387)
    values = reconstruct(model, mask_of(field), rows, args.gp)
    if n == 53:
        order = (1 << n)-1
        if any(order % k == 0 for k in range(2, 6361)):
            raise ArithmeticError("degree-53 index floor failed")
        if args.logs:
            logs = read_logs(args.logs)
        else:
            with EXAMPLE.open(newline="") as stream:
                example = csv.DictReader(stream)
                if example.fieldnames != ["mask", "exponent"]:
                    raise ValueError("invalid degree-53 example header")
                pairs = [(int(row["mask"]), int(row["exponent"])) for row in example]
            if [mask for mask, _ in pairs] != values:
                raise ArithmeticError("degree-53 target masks disagree with the elliptic norms")
            logs = {i: e for i, (_, e) in enumerate(pairs)}
        verify_logs(values, logs, field, None, 1, order)
        if 0 in logs and point_score(n, d, len(logs), 6361, WEIGHTS53) > n:
            print(f"Degree 53 is primitive from {len(logs)} checked elliptic logarithms.")
        else:
            print(f"Verified {len(logs)} partial degree-53 logarithms.")
        if args.logs is None:
            if (set(logs) != set(range(38)) or point_score(n, d, 30, 6361, WEIGHTS53) <= n
                    or point_score(n, d, 38, 107, (12, 28, 12)) <= n):
                raise ArithmeticError("the published degree-53 certificates fall short")
            print("The first 30 suffice after trial division through 6360. All 38 suffice with index floor 107.")
        return
    stream = gzip.open(UNCONDITIONAL_TARGETS, "rt", newline="") if args.no_order_tests else TARGETS.open(newline="")
    with stream:
        records = list(csv.reader(stream))
    if records != [["target", "period_mask_hex"]] + [[str(i), hex(v)] for i, v in enumerate(values)]:
        raise ArithmeticError("published period masks disagree with the elliptic norms")
    if args.no_order_tests:
        floor = 30*n+1
        if (any(gcd((1 << n)-1, 2*j*n+1) != 1 for j in range(1, 15))
                or not quadratic_bound(n, 1 << d, rows, floor)):
            raise ArithmeticError("the degree-1229 two-moment certificate failed")
        print(f"Verified {rows} degree-1229 targets with index floor {floor} and no root-order tests.")
    else:
        score = point_score(n, d, rows, EXTENDED_BOUND+1, WEIGHTS1229)
        if score <= n:
            raise ArithmeticError("insufficient number of split rational places")
        print(f"Verified {rows} elliptic targets in degree 1229. Conditional point bound {score} > {n}.")
    if args.logs:
        taps = CANDIDATES[args.candidate] if args.candidate else args.taps
        f = modulus(n, taps)
        if not irreducible(f):
            raise ValueError("the proposed candidate is reducible")
        if not args.no_order_tests:
            check_known_order(f)
        logs = read_logs(args.logs)
        verify_logs(values, logs, f, coordinate(f), KNOWN if args.projected else 1,
                    COFACTOR if args.projected else (1 << n)-1)
        print(f"Verified {len(logs)} candidate logarithms.")
        if len(logs) == rows and not args.no_order_tests:
            from batch_degree_1229 import verify_published
            from check_degree_1229 import check as check_order
            check_order(10**10, taps)
            verify_published()
            if verify_extension() != EXTENDED_BOUND:
                raise ArithmeticError("degree-1229 index floor failed")
        if len(logs) == rows:
            print("Full order proved for the submitted degree-1229 candidate.")


if __name__ == "__main__":
    main()
