"""Generate binary factor-base relations from norm circles and trace lines in the auxiliary fields."""

import argparse
import csv
import json
import sys
from collections import Counter

from check_1229_frobenius_models import TABLE
from check_degree_1229 import GROUP
from check_factor_base import DATA, irreducible, polynomial
from find_factor_base_logs import insert
from period_coordinate import mask_of


RELATIONS = DATA / "degree-1229-circle-pivots.csv"
HEADER = ("q", "family", "numerator", "denominator", "constant_polynomial", "terms", "pivot")
# A reciprocal gives the inverse norm, and translation by one preserves the trace.
MAPS = {"norm": ((2, 1), (3, 1), (2, 3)), "trace": ((2, 1), (1, 2), (1, 3))}


def homogeneous(p, u, v):
    """Return v^d p(u/v) in the polynomial ring, including common factors."""
    h = u*0 + 1
    vp = v
    for i in range(p.degree()-1, -1, -1):
        h *= u
        if p[i]:
            h += vp
        if i:
            vp *= v
    return h


def pairs(family, a1, a2, b1, b2):
    if family == "norm":
        return a1*a2, b1*b2
    return a1*b2 + a2*b1, b1*b2


def relations(record):
    q = record["q"]
    s = q.bit_length()-1
    modulus = polynomial(int(record["modulus_hex"], 16))
    x = polynomial(2)
    h0 = polynomial(record["numerator_mask"])
    h1 = polynomial(record["denominator_mask"])
    h1_factors = h1.factor()[1]
    y = x**q % modulus
    if x*h1.compose_mod(y, modulus) % modulus != h0.compose_mod(y, modulus):
        raise ArithmeticError("the Frobenius equation fails in this field")
    constants = [polynomial(mask) for d in range(1, s+1) if s % d == 0
                 for mask in range(1 << d, 2 << d) if irreducible(polynomial(mask))]
    if sum(p.degree() for p in constants) != q:
        raise ArithmeticError("incomplete enumeration of constants")
    for family, maps in MAPS.items():
        for am, bm in maps:
            a, b = polynomial(am), polynomial(bm)
            ah = h0*int(a[1]) + h1*int(a[0])
            bh = h0*int(b[1]) + h1*int(b[0])
            lu, lv = pairs(family, a, a**q, b, b**q)
            ru, rv = pairs(family, ah, a, bh, b)
            for p in constants:
                if family == "norm" and p == x:
                    continue
                right = homogeneous(p, ru, rv)
                right_factors = right.factor()[1]
                if any(2*s % g.degree() for g, _ in right_factors):
                    continue
                left = homogeneous(p, lu, lv)
                left_factors = left.factor()[1]
                if any(2*s % g.degree() for g, _ in left_factors + h1_factors):
                    raise ArithmeticError("a circle or line escaped the constant field")
                if (left * (h1**p.degree()).compose_mod(y, modulus) % modulus
                        != right.compose_mod(y, modulus)):
                    raise ArithmeticError("the homogenized identity failed in the target field")
                row = Counter({mask_of(g): e for g, e in left_factors})
                for g, e in h1_factors:
                    row[mask_of(g)] += q*p.degree()*e
                for g, e in right_factors:
                    row[mask_of(g)] -= q*e
                yield (q, family, am, bm, mask_of(p)), {i: e for i, e in row.items() if e}


def rows(records, emit_relations):
    result = []
    for record in records:
        pivots = {}
        for parameters, row in relations(record):
            before = set(pivots)
            if insert(row, pivots, GROUP, fixed_x=False):
                pivot, = pivots.keys()-before
                result.append((*parameters, len(row), pivot))
                if emit_relations:
                    print(json.dumps({"q": record["q"], "terms": sorted(row.items())}, separators=(",", ":")))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--emit", action="store_true", help="emit the pivot table as CSV")
    selection.add_argument("--relations", action="store_true", help="emit independent integer relations as JSONL")
    parser.add_argument("--q", choices=(256, 1024), type=int, help="restrict the calculation to one model")
    args = parser.parse_args()
    records = [r for r in json.loads(TABLE.read_text()) if args.q is None or r["q"] == args.q]
    verified = rows(records, args.relations)
    if args.emit:
        writer = csv.writer(sys.stdout, lineterminator="\n")
        writer.writerow(HEADER)
        writer.writerows(verified)
    elif not args.relations:
        with RELATIONS.open(newline="") as source:
            data = csv.DictReader(source)
            if tuple(data.fieldnames) != HEADER:
                raise ValueError("incorrect pivot table columns")
            expected = [tuple(row.values()) for row in data if args.q is None or int(row["q"]) == args.q]
        if expected != [tuple(map(str, row)) for row in verified]:
            raise ArithmeticError("the published pivot table differs from regeneration")
        for q in (r["q"] for r in records):
            print(f"q = {q}, {sum(row[0] == q for row in verified)} independent relations.")
