"""Certify the conductor prime in twisted cyclotomic root orders with binary quadratic forms."""

import argparse
import ast
import json
from pathlib import Path

from check_translation_lift_orders import X, cyclotomic_form
from check_twisted_ray import eligible, run_gp


DATA = Path(__file__).resolve().parents[1] / "data" / "translation-lift-orders.json"


def conductor_test(gp, p, exponent):
    h, principal, form = ast.literal_eval(run_gp(gp, f"twisted_conductor_class({p},{exponent})"))
    a, b, c = form
    delta = -3 * p if p % 8 == 5 else -p
    if b * b - 4 * a * c != delta * p**2 or bool(principal) != (a == 1):
        raise ValueError(f"invalid reduced form at p={p}")
    return h, bool(principal) or p % 24 == 23


def check_large(gp):
    rows = json.loads(DATA.read_text())["imaginary_quadratic_principalization"]
    for k, h in rows.items():
        p = (1 << int(k)) + 5
        verified_h, index_divisible = conductor_test(gp, p, h)
        if verified_h != h or index_divisible or pow(2, p - 1, p * p) == 1:
            raise ValueError(f"conductor prime valuation mismatch at k={k}")
        print(f"C_{k}: the prime {p} divides the root order exactly once.")


def check_small(gp):
    tested = []
    missing = []
    for p in range(5, 2054, 2):
        if not eligible(p):
            continue
        _, predicted = conductor_test(gp, p, 0)
        power = X.pow_mod(((1 << (p - 1)) - 1) // p, cyclotomic_form(p))
        if (power == 1) != predicted:
            raise ValueError(f"quadratic form and direct powering disagree at p={p}")
        tested.append(p)
        if predicted:
            missing.append(p)
    print(f"Checked {len(tested)} conductor primes by direct powering; "
          f"{len(missing)} divide the root-order index.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    parser.add_argument("--small", action="store_true", help="also compare every eligible p through 2053")
    args = parser.parse_args()
    check_large(args.gp)
    if args.small:
        check_small(args.gp)
