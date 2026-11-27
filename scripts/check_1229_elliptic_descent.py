"""Reduce factors in the two logarithm formulas for the degree-1229 elliptic pentanomial."""

import argparse
import json
from collections import Counter
from functools import cache
from math import gcd
from pathlib import Path

from check_1229_dyadic import halving_relation
from check_1229_frobenius_curves import ELLIPTIC_TAPS
from check_1229_hermitian_descent import (
    F, H0, H1, K, Q, binary_factors, bits, coefficient_norm, element, relation, scalar_groups,
)
from check_1229_isogeny_logs import pullback
from check_1229_log_descent import reduce_task
from check_1229_power_images import SPLITS, split_coefficients, split_log_table
from check_1229_seventh_descent import expand_index, substitute
from check_degree_1229 import COFACTOR, KNOWN
from check_factor_base import DATA, polynomial
from period_coordinate import mask_of
from prepare_1229_single_log import prepare


CERTIFICATE = DATA / "degree-1229-elliptic-pencils.json"


def factor_degrees(mask):
    binary = mask.bit_length() - 1
    return binary // gcd(binary, 20), binary


@cache
def trace_orbits(e):
    """One representative and its orbit size under 2^e in the trace-one line."""
    torus, _ = scalar_groups()
    line = {bits(c/(1+c)) for c in torus if not c.is_one()}
    if len(line) != Q:
        raise ArithmeticError("incorrect size of the trace-one line")
    orbits = []
    while line:
        start = c = element(min(line))
        length = 0
        while True:
            if c + c**Q != F.one():
                raise ArithmeticError("a fibre constant has incorrect trace")
            line.remove(bits(c))
            length += 1
            c = c.frobenius(e)
            if c == start:
                break
        orbits.append((start, length))
    return orbits


def field_product(factors, field):
    value = polynomial(1)
    for p, multiplicity in factors.items():
        value = value * polynomial(p).pow_mod(multiplicity, field) % field
    return value


def subfield_relation(mask, row, field):
    e = row["coefficient_degree"]
    if e <= 0 or 20 % e:
        raise ValueError("incorrect subfield degree")
    g, h = (K([element(c) for c in row[key]]) for key in ("g", "h"))
    m = max(g.degree(), h.degree())
    if (m < 1 or m != row["height"] or g.is_zero() or not g.gcd(h).is_one()
            or any(c.frobenius(e) != c for c in g.coeffs()+h.coeffs())):
        raise ValueError("invalid coprime pencil over the declared subfield")

    def homogeneous(p):
        return sum((c*H0**i*H1**(m-i) for i, c in enumerate(p.coeffs())), K.zero())

    def conjugate(p):
        return K([c**Q for c in p.coeffs()])

    numerator = homogeneous(g)*conjugate(g+h) + homogeneous(h)*conjugate(g)
    if numerator.is_zero():
        raise ArithmeticError("the substituted pencil vanishes identically")
    right = binary_factors(coefficient_norm(numerator, e))
    left = Counter(binary_factors(coefficient_norm(g, e)))
    for c, length in trace_orbits(e):
        left.update(binary_factors(coefficient_norm(h+c*g, e*length)))

    den = polynomial(10).pow_mod(e*m*Q, field)
    if field_product(left, field)*den % field != field_product(right, field).pow_mod(Q, field):
        raise ArithmeticError("the unprojected subfield norm identity failed")
    multiplicity = right.pop(mask)
    terms = Counter({p: w*pow(Q, -1, COFACTOR) for p, w in left.items()})
    terms.subtract(right)
    terms.update({2: e*m, 3: 2*e*m})
    scale = pow(multiplicity, -1, COFACTOR)
    terms = {p: w*scale % COFACTOR for p, w in terms.items() if w % COFACTOR}
    if any(factor_degrees(p)[0] > m for p in terms):
        raise ArithmeticError("a pencil factor exceeds the claimed relative degree")
    return terms


def cubic_relation(mask, row):
    parent = int(row["mask_hex"], 16)
    terms = Counter(relation(parent, row))
    if mask == parent == 0x67:
        return terms
    if (mask, parent) != (0xd, 0x43) or binary_factors(polynomial(pullback(mask))) != {mask: 1, parent: 1, 0x61: 1}:
        raise ArithmeticError("the cubic pullback has unexpected factors")
    terms.update({0x61: 1, 2: -3, 3: -6})
    scale = Q*pow(1-Q, -1, COFACTOR)
    return {p: scale*c % COFACTOR for p, c in terms.items() if c % COFACTOR}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", type=Path, help="compiled degree_1229_dyadic.cpp for the even-degree targets")
    parser.add_argument("--target", type=lambda s: int(s, 0), help="check one of the certified parent masks")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--eight", action="store_true", help="lower both cubics in the eight-input split")
    mode.add_argument("--lower-eight", action="store_true", help="lower each factor in the eight-input split")
    parser.add_argument("--json", action="store_true", help="export all residual logarithm masks and coefficients")
    parser.add_argument("--logs", type=Path, help="verify a mask,exponent CSV of residual logarithms")
    args = parser.parse_args()
    cert = json.loads(CERTIFICATE.read_text())
    cubics = {int(k, 16): v for k, v in cert["eight_cubic_pencils"].items()}
    eight_forms = {int(r["mask_hex"], 16): r for r in cert["eight_pencils"]}
    eight_halvings = {int(k, 16): v for k, v in cert["eight_halving_indices"].items()}
    eight_parents = cubics.keys() | eight_forms.keys() | eight_halvings.keys()
    eight = args.eight or args.lower_eight or args.target in eight_parents
    split = json.loads((DATA / SPLITS["elliptic-eight" if eight else "elliptic"]).read_text())
    original = {int(r["mask_hex"], 16) for r in split["logarithms"]["remaining"]}
    if eight:
        forms, halvings = eight_forms, eight_halvings
        if set(cubics) != {0xd, 0x67} or eight_parents != original or len(original) != 8:
            raise ValueError("the certificate must cover the eight distinct original factors")
        supported = eight_parents if args.lower_eight or args.target is not None else set(cubics)
    else:
        forms = {int(r["mask_hex"], 16): r for r in cert["pencils"]}
        halvings = {int(k, 16): v for k, v in cert["halving_indices"].items()}
        supported = forms.keys() | halvings.keys()
        if forms.keys() & halvings.keys() or supported != original or len(original) != 10:
            raise ValueError("the certificate must cover the ten distinct original factors")
    if args.target is not None and args.target not in supported:
        parser.error("unrecognized elliptic descent target")
    selected = [args.target] if args.target is not None else sorted(supported)
    if args.lower_eight:
        # Later steps also reduce any original parents introduced by earlier steps.
        selected.sort(key=factor_degrees, reverse=True)
    if any(mask in halvings for mask in selected) and not args.backend:
        parser.error("the selected even-degree halving requires --backend")

    _, field, _, root = prepare(ELLIPTIC_TAPS)
    field_mask, table = split_log_table()
    if mask_of(field) != field_mask:
        raise ArithmeticError("the elliptic root uses a different factor-base field")
    whole = args.target is None
    if whole:
        target, name = root, "elliptic"
        weights = Counter(split_coefficients(split, field, root, ELLIPTIC_TAPS))
    else:
        target, name = polynomial(args.target), hex(args.target)
        weights = Counter({args.target: 1})
    for mask in selected:
        if mask in cubics:
            terms = cubic_relation(mask, cubics[mask])
        elif mask in halvings:
            edges = expand_index(args.backend, field_mask, mask, halvings[mask])
            terms = halving_relation(mask, edges, field)
        else:
            terms = subfield_relation(mask, forms[mask], field)
        if eight and any(factor_degrees(p) >= factor_degrees(mask) for p in terms if p not in table):
            raise ArithmeticError("a residual elliptic logarithm was not lowered")
        substitute(weights, mask, terms)

    base = polynomial(2).pow_mod(KNOWN, field)
    result = reduce_task(name, target, weights, table, base, field, args.logs)
    if whole and not result["remaining"]:
        result["exact_index"] = str(gcd(int(result["known_exponent_mod_C"]), COFACTOR))
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        counts = Counter(r["relative_degree"] for r in result["remaining"])
        print(f"{name} has {sum(counts.values())} remaining projected logarithms.")
        for d, n in sorted(counts.items()):
            print(f"Relative degree {d:2d}   {n}")
        if "exact_index" in result:
            print(f"Exact multiplicative index {result['exact_index']}")


if __name__ == "__main__":
    try:
        main()
    finally:
        # Release cached FLINT elements before their coefficient field is destroyed.
        trace_orbits.cache_clear()
        scalar_groups.cache_clear()
        del H0, H1, K, F
