"""Check degree-1229 polynomial identities, reconstruct targets, and verify period-coordinate logs."""

import argparse
import csv
import json
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path

from check_factor_base import DATA, irreducible, irreducible_counts, modulus, moment_bound, polynomial
from find_factor_base_logs import insert
from period_coordinate import CANDIDATES, DEGREE, PRIME, coordinate, frobenius_indices, period_polynomial


ORDER = (1 << DEGREE) - 1
RELATIONS = DATA / "degree-1229-period-relations.jsonl"
TARGETS = DATA / "degree-1229-period-targets.csv"
INDEX_FLOOR = 86483186594349058


def small_irreducibles():
    masks = {p for p in range(2, 1 << 17) if irreducible(polynomial(p))}
    if Counter(p.bit_length()-1 for p in masks) != irreducible_counts(16):
        raise ArithmeticError("incomplete enumeration of small irreducibles")
    return masks


def read_relations(masks):
    """Each triple (m,b,e) contributes B_b(D_m(a))^e to a product equal to one."""
    indices = frobenius_indices(DEGREE)
    psi = period_polynomial(DEGREE)
    x = polynomial(2)
    dickson = [polynomial(0), x]
    for _ in range(2, DEGREE+1):
        dickson.append((x*dickson[-1] + dickson[-2]) % psi)

    @lru_cache(maxsize=32768)
    def value(m, b):
        if min(m, PRIME-m) == 1:
            return polynomial(b)
        return polynomial(b).compose_mod(dickson[min(m, PRIME-m)], psi)

    pivots = {}
    with RELATIONS.open() as rows:
        for line, raw in enumerate(rows, 1):
            left = right = polynomial(1)
            row = Counter()
            for m, b, e in json.loads(raw):
                if m not in indices or b not in masks or not isinstance(e, int) or e == 0:
                    raise ValueError(f"invalid term on relation line {line}")
                v = value(m, b)
                if abs(e) > 1:
                    v = v.pow_mod(abs(e), psi)
                if e > 0:
                    left = left * v % psi
                else:
                    right = right * v % psi
                row[b] += e << indices[m]
            if left != right:
                raise ValueError(f"polynomial identity failed on relation line {line}")
            if not insert(row, pivots, ORDER, fixed_x=False):
                raise ValueError(f"no new unit pivot on relation line {line}")
    return pivots


def closure(pivots, supplied):
    have = set(supplied)
    for p, row in sorted(pivots.items()):
        if row.keys() - {p} <= have:
            have.add(p)
    return have


def select_targets(masks, pivots):
    """Supply the free low columns, then greedily unlock 276 degree-16 columns."""
    low = {p for p in masks if p < 1 << 16}
    targets = low - pivots.keys()
    have = closure(pivots, targets)
    if not low <= have:
        raise ArithmeticError("the low-degree pivots did not close")
    deps = {}
    for p in sorted(masks-have):
        if p in pivots:
            deps[p] = set().union(*(deps.get(q, set()) for q in pivots[p] if q != p))
        else:
            deps[p] = {p}
    while len(have-low) < 276:
        singles = Counter(next(iter(s)) for s in deps.values() if len(s) == 1)
        chosen = min(singles, key=lambda p: (-singles[p], p))
        targets.add(chosen)
        for p in list(deps):
            deps[p].discard(chosen)
            if not deps[p]:
                have.add(p)
                del deps[p]
    if closure(pivots, targets) != have:
        raise ArithmeticError("target selection disagrees with direct triangular substitution")
    return targets, have


def write_targets(targets):
    out = csv.writer(sys.stdout, lineterminator="\n")
    out.writerow(("mask", "degree"))
    out.writerows((p, p.bit_length()-1) for p in sorted(targets))


def verify_submissions(name, paths, pivots, masks):
    f = modulus(DEGREE, CANDIDATES[name])
    r = polynomial(2)
    a = coordinate(f)
    logs = {}

    def check_log(p, e):
        if p not in masks or not 0 <= e < ORDER:
            raise ValueError(f"out-of-range mask or exponent for {p}")
        if r.pow_mod(e, f) != polynomial(p).compose_mod(a, f):
            raise ValueError(f"incorrect {name} period-coordinate logarithm for mask {p}")
        logs[p] = e

    for path in paths:
        with path.open(newline="") as source:
            reader = csv.DictReader(source)
            if reader.fieldnames != ["mask", "exponent"]:
                raise ValueError(f"expected the columns mask,exponent in {path}")
            for row in reader:
                if None in row:
                    raise ValueError(f"extra CSV column in {path}")
                check_log(int(row["mask"]), int(row["exponent"]))
    given = len(logs)
    for p, row in sorted(pivots.items()):
        if p not in logs and row.keys()-{p} <= logs.keys():
            e = -sum(c * logs[q] for q, c in row.items() if q != p) % ORDER
            check_log(p, e)
    counts = Counter(p.bit_length()-1 for p in logs)
    print(f"{name}: {given} supplied and {len(logs)-given} derived logarithms checked.")
    if moment_bound(counts, INDEX_FLOOR, 129, 3) > DEGREE-2:
        from batch_degree_1229 import verify_published
        from check_degree_1229 import check as check_order
        check_order(10**10, CANDIDATES[name])
        if verify_published() + 1 != INDEX_FLOOR:
            raise ArithmeticError("the index hypothesis failed")
        print(f"Full order proved for the {name} candidate.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list-targets", action="store_true", help="emit the target CSV")
    parser.add_argument("--candidate", choices=CANDIDATES, help="sparse modulus used for submitted exponents")
    parser.add_argument("--logs", nargs="+", type=Path, help="verify supplied powers of the sparse root")
    args = parser.parse_args()
    if bool(args.logs) != bool(args.candidate) or (args.list_targets and args.logs):
        parser.error("log submissions require a candidate and at least one CSV")
    masks = small_irreducibles()
    pivots = read_relations(masks)
    targets, covered = select_targets(masks, pivots)
    counts = Counter(p.bit_length()-1 for p in covered)
    score = moment_bound(counts, INDEX_FLOOR, 129, 3)
    if score <= DEGREE-2:
        raise ArithmeticError("covered degree counts fall short of the character bound")
    if args.list_targets:
        write_targets(targets)
    else:
        with TARGETS.open(newline="") as source:
            rows = list(csv.reader(source))
        if rows != [["mask", "degree"]] + [[str(p), str(p.bit_length()-1)] for p in sorted(targets)]:
            raise ArithmeticError("the published target list differs from reconstruction")
        print(f"{len(pivots)} polynomial identities and unit pivots verified. "
              f"{len(targets)} inputs imply {len(covered)} polynomial logarithms.")
        print(f"Their conditional moment score is {score} > {DEGREE-2}.")
        if args.logs:
            verify_submissions(args.candidate, args.logs, pivots, masks)
