"""Verify sparse-root decompositions and export or check their individual projected-log tasks."""

import argparse
import csv
import json
from collections import Counter
from math import gcd
from pathlib import Path

from check_1229_factor_base_orders import read_table
from check_1229_isogeny_logs import H0, H1, Q
from check_degree_1229 import COFACTOR, KNOWN, check_known_order
from check_factor_base import DATA, irreducible, modulus, polynomial
from period_coordinate import CANDIDATES, mask_of


CERT = DATA / "degree-1229-log-descent.json"
PENCIL_NAMES = {"degree-7": 0x91, "degree-11": 0xc19}


def factors(poly):
    if poly.is_zero():
        raise ValueError("zero polynomial in a multiplicative relation")
    return Counter({mask_of(p): int(e) for p, e in poly.factor()[1]})


def homogeneous(poly, a, b, degree):
    return sum((a**i * b**(degree-i) for i in range(poly.degree()+1) if poly[i]), polynomial(0))


def sparse_quotient(name, row, field):
    sparse = modulus(1229, CANDIDATES[name])
    if not irreducible(sparse):
        raise ValueError("the proposed sparse polynomial is reducible")
    check_known_order(sparse)
    task = json.loads((DATA / f"degree-1229-single-log-{name}.json").read_text())
    if int(task["model_modulus_hex"], 16) != mask_of(field):
        raise ValueError("the sparse root uses another model modulus")
    root = polynomial(int(task["sparse_root_in_model_hex"], 16))
    u, v = (polynomial(int(row[k], 16)) for k in ("numerator_hex", "denominator_hex"))
    if (u.degree() >= 1229 or v.degree() >= 1229 or u.gcd(v) != 1
            or sparse.compose_mod(root, field) != 0 or (v*root-u) % field != 0):
        raise ArithmeticError("the reduced quotient does not represent the designated sparse root")
    relation = factors(u)
    relation.subtract(factors(v))
    return root, relation


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
    source = factors(f**(Q+1) + g**(Q+1))
    inverse_q = pow(Q, -1, COFACTOR)
    relation = Counter({p: e*inverse_q for p, e in source.items()})
    relation.update({p: m*e for p, e in factors(H1).items()})
    relation.subtract(rhs)
    inv = pow(multiplicity, -1, COFACTOR)
    return target, {p: inv*c for p, c in relation.items()}


def submitted(path, required, base, field):
    result = {}
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream)
        if reader.fieldnames != ["mask", "exponent"]:
            raise ValueError("expected mask,exponent columns")
        for row in reader:
            p, e = int(row["mask"], 0), int(row["exponent"])
            if p not in required or p in result or not 0 <= e < COFACTOR:
                raise ValueError(f"unexpected, repeated or out-of-range logarithm at {p:#x}")
            if base.pow_mod(e, field) != polynomial(p).pow_mod(KNOWN, field):
                raise ArithmeticError(f"incorrect projected logarithm at {p:#x}")
            result[p] = e
    return result


def reduce_task(name, target, relation, table, base, field, path):
    coeffs = {p: c % COFACTOR for p, c in relation.items() if c % COFACTOR}
    known = {p: table[p] for p in coeffs if p in table}
    if path:
        known.update(submitted(path, coeffs.keys()-known.keys(), base, field))
    offset = sum(coeffs[p]*e for p, e in known.items()) % COFACTOR
    value = base.pow_mod(offset, field)
    todo = []
    for p in sorted(coeffs.keys()-known.keys()):
        deg = p.bit_length()-1
        weight = coeffs[p]
        projected = polynomial(p).pow_mod(KNOWN, field)
        value = (value * projected.pow_mod(weight, field)) % field
        todo.append({"mask_hex": hex(p), "relative_degree": deg//gcd(deg, 20),
                     "coefficient_mod_C": str(weight)})
    if value != target.pow_mod(KNOWN, field):
        raise ArithmeticError(f"the assembled projected relation for {name} failed in the field")
    result = {"task": name, "model_modulus_hex": hex(mask_of(field)), "K": str(KNOWN), "C": str(COFACTOR),
              "base_hex": hex(mask_of(base)), "target_hex": hex(mask_of(value)),
              "known_exponent_mod_C": str(offset), "remaining": todo}
    if name in CANDIDATES and not todo:
        result["exact_index"] = str(gcd(offset, COFACTOR))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task", choices=(*CANDIDATES, *PENCIL_NAMES))
    parser.add_argument("--json", action="store_true", help="print the complete selected task")
    parser.add_argument("--logs", type=Path, help="check a mask,exponent CSV for the selected task")
    args = parser.parse_args()
    if (args.json or args.logs) and not args.task:
        parser.error("--json and --logs require --task")
    field_mask, table = read_table()
    field = polynomial(field_mask)
    base = polynomial(2).pow_mod(KNOWN, field)
    cert = json.loads(CERT.read_text())
    for name in ([args.task] if args.task else [*CANDIDATES, *PENCIL_NAMES]):
        if name in CANDIDATES:
            target, relation = sparse_quotient(name, cert["quotients"][name], field)
        else:
            row, = (r for r in cert["pencils"] if int(r["target_hex"], 16) == PENCIL_NAMES[name])
            target, relation = norm_pencil(row)
        result = reduce_task(name, target, relation, table, base, field, args.logs)
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
