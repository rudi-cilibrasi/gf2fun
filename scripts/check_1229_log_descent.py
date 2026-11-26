"""Verify sparse-root decompositions and export or check their individual projected-log tasks."""

import argparse
import json
from collections import Counter
from functools import cache
from math import gcd
from pathlib import Path

from check_1229_factor_base_orders import CIRCLE_LOGS, ISOGENY_LOGS, check_examples, read_logs, read_table
from check_1229_hermitian_descent import records as hermitian_records, relation as hermitian_relation
from check_1229_isogeny_logs import H0, H1, Q
from check_1229_norm_height import FORMS, norm_quotient, sparse_root
from check_degree_1229 import COFACTOR, KNOWN
from check_factor_base import DATA, irreducible, polynomial
from period_coordinate import CANDIDATES, mask_of


CERT = DATA / "degree-1229-log-descent.json"
PENCIL_NAMES = {
    "degree-7": 0x91, "degree-11": 0xc19,
    "seroussi-0xd3": 0xd3, "product-0xbf": 0xbf, "product-0x35d5": 0x35d5,
}


def factors(poly):
    if poly.is_zero():
        raise ValueError("zero polynomial in a multiplicative relation")
    return Counter({mask_of(p): int(e) for p, e in poly.factor()[1]})


def homogeneous(poly, a, b, degree):
    return sum((a**i * b**(degree-i) for i in range(poly.degree()+1) if poly[i]), polynomial(0))


@cache
def unity_factors():
    return (polynomial(2)**(Q+1) + 1).factor()[1]


def sparse_quotient(root, row, field):
    u, v = (polynomial(int(row[k], 16)) for k in ("numerator_hex", "denominator_hex"))
    if (u.degree() >= 1229 or v.degree() >= 1229 or u.gcd(v) != 1
            or (v*root-u) % field != 0):
        raise ArithmeticError("the reduced quotient does not represent the designated sparse root")
    relation = factors(u)
    relation.subtract(factors(v))
    return relation


def norm_pencil(row):
    target, f, g = (polynomial(int(row[k], 16)) for k in ("target_hex", "f_hex", "g_hex"))
    m = max(f.degree(), g.degree())
    if f.gcd(g) != 1 or not irreducible(target):
        raise ValueError("invalid pencil or target")
    # F(x)^(q+1) + G(x)^(q+1) evaluated at y=x^q, after clearing h1(y)^m.
    numerator = f*homogeneous(f, H0, H1, m) + g*homogeneous(g, H0, H1, m)
    rhs = factors(numerator)
    multiplicity = rhs.pop(mask_of(target), 0)
    if gcd(multiplicity, COFACTOR) != 1:
        raise ArithmeticError("the pencil does not isolate its target")
    # Homogenize each small binary factor of T^(q+1)+1 before factoring the pencil.
    source = Counter()
    for u, exponent_in_unity in unity_factors():
        piece = homogeneous(u, f, g, u.degree())
        for p, exponent in factors(piece).items():
            source[p] += int(exponent_in_unity) * exponent
    inverse_q = pow(Q, -1, COFACTOR)
    relation = Counter({p: e*inverse_q for p, e in source.items()})
    relation.update({p: m*e for p, e in factors(H1).items()})
    relation.subtract(rhs)
    inv = pow(multiplicity, -1, COFACTOR)
    return target, {p: inv*c for p, c in relation.items()}


def seroussi_binomial():
    shift = polynomial(3)
    # (1+x)^36 / (1+y)^5 = (1+x)^(-5084) and 5084 = 4*1271.
    d = (H0+H1)**36 + H1**36 * shift**5
    rhs = factors(d)
    if rhs.pop(0xd3, 0) != 1:
        raise ArithmeticError("the binomial does not isolate the designated factor")
    inverse_q = pow(Q, -1, COFACTOR)
    source = factors(shift**1271 + 1)
    relation = Counter({p: 4*inverse_q*e for p, e in source.items()})
    relation.update({3: 5-5084*inverse_q})
    relation.update({p: 36*e for p, e in factors(H1).items()})
    relation.subtract(rhs)
    return polynomial(0xd3), relation


def checked_exponent(p, e, base, field):
    if not 0 <= e < COFACTOR:
        raise ValueError(f"out-of-range logarithm at {p:#x}")
    if base.pow_mod(e, field) != polynomial(p).pow_mod(KNOWN, field):
        raise ArithmeticError(f"incorrect projected logarithm at {p:#x}")
    return e


def submitted(path, required, base, field):
    result = {}
    for p, e in read_logs(path):
        if p not in required or p in result:
            raise ValueError(f"unexpected or repeated logarithm at {p:#x}")
        result[p] = checked_exponent(p, e, base, field)
    return result


def reduce_task(name, target, relation, table, base, field, path):
    coeffs = {p: c % COFACTOR for p, c in relation.items() if c % COFACTOR}
    known = {p: table[p] for p in coeffs if p in table}
    if path:
        known.update(submitted(path, coeffs.keys()-known.keys(), base, field))
    offset = sum(coeffs[p]*e for p, e in known.items()) % COFACTOR
    value = base.pow_mod(offset, field)
    todo = []
    products = {}
    for p in sorted(coeffs.keys()-known.keys()):
        deg = p.bit_length()-1
        weight = coeffs[p]
        products[weight] = (products.get(weight, polynomial(1)) * polynomial(p)) % field
        todo.append({"mask_hex": hex(p), "relative_degree": deg//gcd(deg, 20),
                     "coefficient_mod_C": str(weight)})
    for weight, prod in products.items():
        value = (value * prod.pow_mod(KNOWN * weight, field)) % field
    if value != target.pow_mod(KNOWN, field):
        raise ArithmeticError(f"the assembled projected relation for {name} failed in the field")
    result = {"task": name, "model_modulus_hex": hex(mask_of(field)), "K": str(KNOWN), "C": str(COFACTOR),
              "base_hex": hex(mask_of(base)), "target_hex": hex(mask_of(value)),
              "known_exponent_mod_C": str(offset), "remaining": todo}
    if name in CANDIDATES and not todo:
        result["exact_index"] = str(gcd(offset, COFACTOR))
    return result


def main():
    forms = hermitian_records()
    cubics = {p for p, row in forms.items() if len(row["relative_factor"]) == 4}
    form_names = {f"{'cubic' if p in cubics else 'quadratic'}-{p:#x}": p for p in forms}
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task", choices=(*CANDIDATES, *PENCIL_NAMES, "seroussi-0xd3-binomial", *form_names))
    parser.add_argument("--json", action="store_true", help="print the complete selected task")
    parser.add_argument("--logs", type=Path, help="check a mask,exponent CSV for the selected task")
    parser.add_argument("--norm-form", choices=FORMS,
                        help="use one or two irreducible norms for a whole pentanomial")
    parser.add_argument("--expand-cubics", action="store_true", help="substitute all available cubic descents")
    parser.add_argument("--alternate-pencils", action="store_true",
                        help="use the three alternative pencils containing solved quadratic logarithms")
    parser.add_argument("--terminal-orders", action="store_true",
                        help="also verify the orders and minimal-polynomial weights of the solved quadratics")
    args = parser.parse_args()
    if (args.json or args.logs) and not args.task:
        parser.error("--json and --logs require --task")
    if args.norm_form and args.task and args.task not in CANDIDATES:
        parser.error("--norm-form applies to the product and seroussi pentanomials")
    field_mask, table = read_table()
    extra_logs = dict(read_logs(CIRCLE_LOGS))
    extra_logs.update(read_logs(ISOGENY_LOGS))
    terminal = {p: int(row["log_mod_C"]) for p, row in forms.items() if "log_mod_C" in row}
    if terminal.keys() & (extra_logs.keys() | table.keys()):
        raise ValueError("a terminal logarithm was already in the earlier tables")
    extra_logs.update(terminal)
    if args.terminal_orders:
        if any(gcd(e, COFACTOR) != 1 for e in terminal.values()):
            raise ArithmeticError("a terminal logarithm fails the cofactor order test")
        check_examples(field_mask, terminal, {p: (1, forms[p]["minimal_polynomial_terms"]) for p in terminal})
    field = polynomial(field_mask)
    base = polynomial(2).pow_mod(KNOWN, field)
    cert = json.loads(CERT.read_text())
    @cache
    def hermitian(p):
        row = forms[p]
        if args.alternate_pencils and "alternate_hermitian" in row:
            row = row | {"hermitian": row["alternate_hermitian"]}
        return hermitian_relation(p, row)

    names = list(CANDIDATES) if args.norm_form else [*CANDIDATES, *PENCIL_NAMES, "seroussi-0xd3-binomial", *form_names]
    for name in ([args.task] if args.task else names):
        if name in CANDIDATES:
            target = sparse_root(name, field)
            if args.norm_form:
                relation = norm_quotient(name, args.norm_form, target, field)
            else:
                relation = sparse_quotient(target, cert["quotients"][name], field)
        elif name in form_names:
            p = form_names[name]
            target, relation = polynomial(p), hermitian(p)
        elif name == "seroussi-0xd3-binomial":
            target, relation = seroussi_binomial()
        else:
            row, = (r for r in cert["pencils"] if int(r["target_hex"], 16) == PENCIL_NAMES[name])
            target, relation = norm_pencil(row)
        if args.expand_cubics:
            relation = Counter(relation)
            for p in sorted(relation.keys() & cubics):
                weight = relation.pop(p)
                relation.update({m: weight*c for m, c in hermitian(p).items()})
        for p in (relation.keys() & extra_logs.keys()) - table.keys():
            table[p] = checked_exponent(p, extra_logs[p], base, field)
        result = reduce_task(name, target, relation, table, base, field, args.logs)
        if args.norm_form:
            result["norm_form"] = args.norm_form
        if name in form_names and "log_mod_C" in forms[form_names[name]]:
            if result["remaining"] or result["known_exponent_mod_C"] != forms[form_names[name]]["log_mod_C"]:
                raise ArithmeticError("the circle does not reconstruct the published terminal exponent")
        if args.json:
            print(json.dumps(result, indent=2))
        elif result["remaining"]:
            degrees = [r["relative_degree"] for r in result["remaining"]]
            print(f"{name}: verified {len(degrees)} remaining logarithms of maximum relative degree {max(degrees)}.")
        else:
            e = int(result["known_exponent_mod_C"])
            print(f"{name}: verified projected logarithm {e}.")
            if "exact_index" in result:
                print(f"The sparse root has exact multiplicative-group index {result['exact_index']}.")


if __name__ == "__main__":
    main()
