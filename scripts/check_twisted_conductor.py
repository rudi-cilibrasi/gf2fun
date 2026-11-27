"""Certify the conductor prime in twisted cyclotomic root orders with binary quadratic forms."""

import argparse
import ast
import json
from pathlib import Path

from flint import fmpz_mat

from check_translation_lift_orders import X, cyclotomic_form
from check_twisted_ray import eligible, run_gp


DATA = Path(__file__).resolve().parents[1] / "data" / "translation-lift-orders.json"


def reduced_form(disc, a, b):
    """Reduce a positive definite binary quadratic form of odd discriminant."""
    while True:
        b = (b + a - 1) % (2 * a) - a + 1
        c, remainder = divmod(b * b - disc, 4 * a)
        if remainder:
            raise ValueError("nonintegral quadratic form")
        if a <= c:
            return a, abs(b) if a == c else b, c
        a, b = c, -b


def compose(disc, left, right):
    """Multiply the ideal lattices in the basis w=(1+sqrt(disc))/2, 1."""
    a, b, _ = left
    other_a, other_b, _ = right
    s, t = -(b + 1) // 2, -(other_b + 1) // 2
    # Multiply (a, w+s) by (other_a, w+t), using w²=w+(disc-1)/4.
    norm = a * other_a
    basis = fmpz_mat([[0, norm], [a, a * t], [other_a, other_a * s],
                      [1 + s + t, s * t + (disc - 1) // 4]]).hnf()
    content, offset, integer = int(basis[0, 0]), int(basis[0, 1]), int(basis[1, 1])
    if offset % content or integer * content != norm or integer % content:
        raise ValueError("inconsistent ideal product")
    return reduced_form(disc, integer // content, -2 * (offset // content) - 1)


def form_power(disc, form, exponent):
    result = reduced_form(disc, 1, 1)
    base = form
    while exponent:
        if exponent % 2:
            result = compose(disc, result, base)
        exponent //= 2
        if exponent:
            base = compose(disc, base, base)
    return result


def conductor_test(p, h):
    if h <= 0 or h % p == 0:
        raise ValueError(f"invalid principalization exponent at p={p}")
    delta = -3 * p if p % 8 == 5 else -p
    if form_power(delta, reduced_form(delta, 2, 1), h)[0] != 1:
        raise ValueError(f"prime above two is not principalized at p={p}")
    disc = delta * p**2
    lifted = form_power(disc, reduced_form(disc, 2, 1), h)
    if form_power(disc, lifted, p)[0] != 1:
        raise ValueError(f"lifted class is outside the conductor kernel at p={p}")
    return lifted


def check_large():
    rows = json.loads(DATA.read_text())["imaginary_quadratic_principalization"]
    for k, h in rows.items():
        p = (1 << int(k)) + 5
        if not eligible(p) or p % 24 != 13:
            raise ValueError(f"ineligible conductor at k={k}")
        if conductor_test(p, h)[0] == 1 or pow(2, p - 1, p * p) == 1:
            raise ValueError(f"conductor prime valuation mismatch at k={k}")
        print(f"C_{k}: the prime {p} divides the root order exactly once.")


def check_small(gp):
    tested = []
    missing = []
    for p in range(5, 2054, 2):
        if not eligible(p):
            continue
        h, principal, form = ast.literal_eval(run_gp(gp, f"twisted_conductor_class({p})"))
        lifted = conductor_test(p, h)
        if lifted != tuple(form) or (lifted[0] == 1) != bool(principal):
            raise ValueError(f"PARI and ideal-lattice composition disagree at p={p}")
        predicted = bool(principal) or p % 24 == 23
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
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for the small comparison")
    parser.add_argument("--small", action="store_true", help="also compare every eligible p through 2053")
    args = parser.parse_args()
    check_large()
    if args.small:
        check_small(args.gp)
