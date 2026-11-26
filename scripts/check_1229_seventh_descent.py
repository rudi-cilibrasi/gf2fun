"""Verify smaller logarithm tasks for the four degree-1229 seventh-power candidates."""

import argparse
import gzip
import json
from collections import Counter
from math import gcd
from pathlib import Path

from check_1229_dyadic import halving_relation, native_rows
from check_1229_hermitian_descent import relation, scalar_groups
from check_1229_log_descent import checked_exponent, norm_pencil, reduce_task
from check_1229_power_images import SOURCE, SPLITS, split_coefficients, split_log_table, verify_pair
from check_degree_1229 import COFACTOR, KNOWN
from check_factor_base import DATA, polynomial
from period_coordinate import mask_of
from prepare_1229_single_log import prepare


HALVINGS = DATA / "degree-1229-seventh-power-halvings.json.gz"
PENCILS = DATA / "degree-1229-seventh-power-cubic-pencils.json"
REAL_PENCILS = DATA / "degree-1229-seventh-power-real-pencils.json"
TORUS = {"target_hex": "0x2413", "f_hex": "0xf1", "g_hex": "0xc0"}


def real_pencil_relation(mask, row):
    from check_1229_hermitian_descent import (
        F, H0, H1, K, Q, binary_factors, coefficient_norm, element, product,
    )

    g, h = (K([element(c) for c in row[key]]) for key in ("g", "h"))
    m = max(g.degree(), h.degree())
    if (m < 1 or g.gcd(h).degree() != 0
            or any(c**Q != c for c in g.coeffs()+h.coeffs())):
        raise ValueError("expected a nonconstant coprime pair over F_1024")

    def homogeneous(p):
        return sum((c*H0**i*H1**(m-i) for i, c in enumerate(p.coeffs())), K.zero())

    numerator = homogeneous(g)*(g+h) + homogeneous(h)*g
    right = binary_factors(coefficient_norm(numerator, 10))
    multiplicity = right.pop(mask)
    _, scalars = scalar_groups()
    trace_one = [u for u in scalars if sum((u.frobenius(j) for j in range(10)), F.zero()).is_one()]
    pieces = [g, *(h*h + h*g + u*g*g for u in trace_one)]
    if len(trace_one) != Q//2 or product(pieces) != g**(Q+1) + g**Q*h + g*h**Q:
        raise ArithmeticError("the real fibres did not reconstruct the pencil")
    left = Counter()
    for piece in pieces:
        left.update(binary_factors(coefficient_norm(piece, 10)))
    weights = Counter({p: c*pow(Q, -1, COFACTOR) for p, c in left.items()})
    weights.subtract(right)
    weights.update({2: 10*m, 3: 20*m})  # H1(T) = T (T+1)^2
    inverse = pow(multiplicity, -1, COFACTOR)
    terms = {p: inverse*c % COFACTOR for p, c in weights.items() if c % COFACTOR}
    if any((p.bit_length()-1)//gcd(p.bit_length()-1, 20) > m for p in terms):
        raise ArithmeticError("a real pencil factor exceeds the degree of the pencil")
    return terms


def sextic_relation(mask, row):
    from check_1229_hermitian_descent import K, Q, element, matrix_relation

    g, h = ([element(c) for c in row[key]] for key in ("g", "h"))
    if (len(g) != 6 or len(h) != 6 or any(c**16 != c for c in [*g, *h])
            or K(g).gcd(K(h)).degree() != 0):
        raise ValueError("invalid quintic pencil over F_16")
    matrix = [[g[i]*h[j]**Q+h[i]*g[j]**Q for j in range(6)] for i in range(6)]
    return matrix_relation(mask, row, matrix)


def halving_data():
    with gzip.open(HALVINGS, "rt") as stream:
        parents = {int(p, 16): row for p, row in json.load(stream).items()}
    children = {}
    for parent, row in parents.items():
        edges = [(int(p, 16), left, right, i) for p, left, right, i in row["children"]]
        if (parent.bit_length() != 401 or row["pencil_index"] < 1 or len(edges) != 1029
                or any(p.bit_length() != 201 or i < 1 for p, _, _, i in edges)):
            raise ValueError("invalid halving certificate")
        row["children"] = [(p, left, right) for p, left, right, _ in edges]
        children.update({p: i for p, _, _, i in edges})
    if len(parents) != 2 or len(children) != 2058:
        raise ValueError("the two parents must have distinct children")
    return parents, children


def expand_index(backend, field_mask, mask, index):
    rows = native_rows(backend, "expand-lines", field_mask, [(mask, index)])
    if not rows or any(p != mask for p, *_ in rows):
        raise ValueError("incomplete pencil expansion")
    return [(p, left, right) for _, p, left, right in rows]


def audit_branches(backend, field_mask, parents, children):
    for mask, row in parents.items():
        if expand_index(backend, field_mask, mask, row["pencil_index"]) != row["children"]:
            raise ArithmeticError("the recorded children disagree with the indexed pencil")
    rows = native_rows(backend, "replay-lines", field_mask, children.items())
    if ([p for p, _, _ in rows] != list(children)
            or any(degree != (p.bit_length()-1)//40 or not 1024 <= n <= 1029 for p, n, degree in rows)):
        raise ArithmeticError("a second halving failed to split into linear factors")
    return sum(n for _, n, _ in rows)


def substitute(weights, mask, terms):
    coefficient = weights.pop(mask)
    weights.update({p: coefficient*c for p, c in terms.items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task", default="root", metavar="root|quintic|MASK",
                        help="export the full root task, the quintic, or one binary factor mask")
    parser.add_argument("--quadratics", action="store_true", help="expand all 149 cubics of the quintic")
    parser.add_argument("--real-pencils", action="store_true", help="expand the real odd-degree factors of the root task")
    parser.add_argument("--backend", type=Path, help="compiled scripts/degree_1229_dyadic.cpp")
    parser.add_argument("--audit-branches", action="store_true", help="replay all 2,058 second halvings")
    parser.add_argument("--logs", type=Path, help="verify any subset of a task, as mask,exponent CSV")
    parser.add_argument("--json", action="store_true", help="print the field, base, target and weighted rows")
    args = parser.parse_args()
    forms = json.loads(PENCILS.read_text())
    interpolation = json.loads(REAL_PENCILS.read_text())
    real = {int(row["mask_hex"], 16): row for row in interpolation["forms"]}
    sextic = interpolation["sextic"]
    sextic_mask = int(sextic["mask_hex"], 16)
    extra = {int(p, 16): i for p, i in interpolation["halving_indices"]}
    quintic = int(forms["quintic_hex"], 16)
    cubics = {int(row["mask_hex"], 16): row for row in forms["cubics"]}
    parents, children = halving_data()
    if (len(extra) != 380 or len(extra) != len(interpolation["halving_indices"]) or extra.keys() & children.keys()
            or any(p.bit_length()-1 not in (120, 160, 200) or i < 1 for p, i in extra.items())):
        raise ValueError("invalid interpolation halving index list")
    field_mask, table = split_log_table()
    field = polynomial(field_mask)
    base = polynomial(2).pow_mod(KNOWN, field)
    for key, value in forms["catalogue_logs"].items():
        p = int(key, 16)
        table[p] = checked_exponent(p, int(value), base, field)
    if args.audit_branches:
        if not args.backend:
            parser.error("--audit-branches requires --backend")
        indexed = children | extra if args.real_pencils else children
        count = audit_branches(args.backend, field_mask, parents, indexed)
        print(f"Verified {len(indexed)} degree halvings with {count} linear factors before norms.")
        return
    if args.task == "root":
        mask = None
    elif args.task == "quintic":
        mask = quintic
    else:
        mask = int(args.task, 0)
    if args.quadratics and mask != quintic:
        parser.error("--quadratics applies to --task quintic")
    if args.real_pencils and mask is not None:
        parser.error("--real-pencils applies to the root task")
    if mask is None:
        verify_pair()
        _, model, _, target = prepare(SOURCE)
        if mask_of(model) != field_mask:
            raise ValueError("incorrect field for the sparse root")
        row = json.loads((DATA / SPLITS["degree-20"]).read_text())
        weights = Counter(split_coefficients(row, field, target))
        torus, terms = norm_pencil(TORUS)
        substitute(weights, mask_of(torus), terms)
        for parent, row in parents.items():
            substitute(weights, parent, halving_relation(parent, row["children"], field))
        if args.real_pencils:
            for p, row in real.items():
                substitute(weights, p, real_pencil_relation(p, row))
            substitute(weights, sextic_mask, sextic_relation(sextic_mask, sextic))
            even = {p for p, c in weights.items() if c % COFACTOR and p not in table and p.bit_length()-1 in (120, 160, 200)}
            if even != children.keys() | extra.keys():
                raise ArithmeticError("the archived pencils do not cover the even-degree factors")
    elif mask == quintic:
        target = polynomial(mask)
        weights = Counter(real_pencil_relation(mask, forms))
        remaining = Counter((p.bit_length()-1)//gcd(p.bit_length()-1, 20) for p in weights.keys()-table.keys())
        if remaining != {2: 275, 3: 149} or len(cubics) != 149:
            raise ArithmeticError("unexpected degrees in the quintic pencil")
        if args.quadratics:
            for p, row in cubics.items():
                substitute(weights, p, relation(p, row))
    elif mask in cubics:
        target, weights = polynomial(mask), relation(mask, cubics[mask])
    elif mask in real:
        target, weights = polynomial(mask), real_pencil_relation(mask, real[mask])
    elif mask == sextic_mask:
        target, weights = polynomial(mask), sextic_relation(mask, sextic)
    elif mask == int(TORUS["target_hex"], 16):
        target, weights = norm_pencil(TORUS)
    elif mask in parents:
        target, weights = polynomial(mask), halving_relation(mask, parents[mask]["children"], field)
    elif mask in children or mask in extra:
        if not args.backend:
            parser.error("select --backend to expand an indexed factor")
        index = children[mask] if mask in children else extra[mask]
        edges = expand_index(args.backend, field_mask, mask, index)
        target, weights = polynomial(mask), halving_relation(mask, edges, field)
    else:
        parser.error("no pencil for this mask")
    result = reduce_task(args.task, target, weights, table, base, field, args.logs)
    if mask is None:
        indexed = children | extra
        for row in result["remaining"]:
            p = int(row["mask_hex"], 16)
            if p in indexed:
                row.update(halving_index=indexed[p], halving_relative_degree_bound=(p.bit_length()-1)//40)
    degrees = Counter(r["relative_degree"] for r in result["remaining"])
    if mask == quintic and args.quadratics and any(d > 2 for d in degrees):
        raise ArithmeticError("a cubic survived the descent to quadratics")
    if mask is None and not degrees:
        result["exact_index"] = str(gcd(int(result["known_exponent_mod_C"]), COFACTOR))
    if args.json or not degrees:
        print(json.dumps(result, indent=2))
    else:
        print(f"{args.task}: {sum(degrees.values())} remaining logarithms by relative degree {dict(sorted(degrees.items()))}.")


if __name__ == "__main__":
    try:
        main()
    finally:
        scalar_groups.cache_clear()
