"""Check degree-1229 polynomial identities, reconstruct targets, and verify period-coordinate logs."""

import argparse
import csv
import json
import sys
from collections import Counter
from functools import lru_cache
from math import lcm
from pathlib import Path

from check_factor_base import DATA, irreducible, irreducible_counts, modulus, moment_bound, polynomial
from find_factor_base_logs import insert, recover
from period_coordinate import CANDIDATES, DEGREE, coordinate, frobenius_indices, mask_of, period_polynomial


ORDER = (1 << DEGREE) - 1
RELATIONS = DATA / "degree-1229-period-relations.jsonl"
TARGETS = DATA / "degree-1229-period-targets.csv"
COMPACT_TARGETS = DATA / "degree-1229-period-compact.csv"
INDEX_FLOOR = 86483186594349058


def small_irreducibles(limit=16):
    masks = {p for p in range(2, 1 << (limit+1)) if irreducible(polynomial(p))}
    if Counter(p.bit_length()-1 for p in masks) != irreducible_counts(limit):
        raise ArithmeticError("incomplete enumeration of small irreducibles")
    return masks


def read_relations(masks, n=DEGREE, path=RELATIONS):
    """Each triple (m,b,e) contributes B_b(D_m(a))^e to a product equal to one."""
    p = 2*n + 1
    order = (1 << n) - 1
    indices = frobenius_indices(n)
    psi = period_polynomial(n)
    x = polynomial(2)
    dickson = [polynomial(0), x]
    for _ in range(2, n+1):
        dickson.append((x*dickson[-1] + dickson[-2]) % psi)

    @lru_cache(maxsize=32768)
    def value(m, b):
        if min(m, p-m) == 1:
            return polynomial(b)
        return polynomial(b).compose_mod(dickson[min(m, p-m)], psi)

    pivots = {}
    with path.open() as rows:
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
            if not insert(row, pivots, order, fixed_x=False):
                raise ValueError(f"no new unit pivot on relation line {line}")
    return pivots


def closure(pivots, supplied):
    have = set(supplied)
    for p, row in sorted(pivots.items()):
        if row.keys() - {p} <= have:
            have.add(p)
    return have


def extend_dickson(small, pivots):
    """Factor B(D_m) in F_2[T], keeping relations supported through degree 32."""
    masks = set(small)
    x = polynomial(2)
    dickson = [x*0, x]
    for _ in range(2, 8):
        dickson.append(x*dickson[-1] + dickson[-2])
    indices = frobenius_indices(DEGREE)
    for m in (3, 5, 7):
        for p in sorted(small):
            composed = polynomial(p)(dickson[m])
            factors = composed.factor()[1]
            if any(f.degree() > 32 for f, _ in factors):
                continue
            product = polynomial(1)
            row = {}
            for f, e in factors:
                q = mask_of(f)
                if q not in masks and not irreducible(f):
                    raise ArithmeticError("a higher-degree factor is reducible")
                masks.add(q)
                row[q] = e
                product *= f**e
            if product != composed:
                raise ArithmeticError("incorrect Dickson factorization")
            row[p] = row.get(p, 0) - (1 << indices[m])
            insert(row, pivots, ORDER, fixed_x=False)
    return masks


def select_targets(masks, pivots):
    """Supply free low columns and choose degree-16 inputs by newly available moment weight."""
    low = {p for p in masks if p < 1 << 16}
    targets = low - pivots.keys()
    have = closure(pivots, targets)
    if not low <= have:
        raise ArithmeticError("the low-degree pivots did not close")
    deps = {}
    for p in sorted(masks-have):
        if p in pivots:
            missing = pivots[p].keys() - {p} - have
            if missing <= deps.keys():
                deps[p] = set().union(*(deps[q] for q in missing))
        elif p < 1 << 17:
            deps[p] = {p}
    base = moment_bound({}, INDEX_FLOOR, 129, 3)
    weights = {d: moment_bound({d: 1}, INDEX_FLOOR, 129, 3) - base
               for d in {p.bit_length()-1 for p in masks}}
    scale = lcm(base.denominator, *(w.denominator for w in weights.values()))
    gain = {d: int(scale*w) for d, w in weights.items()}
    score = int(scale*base) + sum(gain[p.bit_length()-1] for p in have)
    while score <= (DEGREE-2)*scale:
        rewards = Counter()
        for p, missing in deps.items():
            if len(missing) == 1:
                rewards[next(iter(missing))] += gain[p.bit_length()-1]
        chosen = min(rewards, key=lambda p: (-rewards[p], p))
        score += rewards[chosen]
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


def read_compact_targets(masks, pivots):
    """Replay the alternative certificate using the same triangular identities."""
    with COMPACT_TARGETS.open(newline="") as source:
        rows = csv.reader(source)
        if next(rows, []) != ["mask", "degree"]:
            raise ValueError("expected a compact target table with columns mask,degree")
        targets = set()
        for mask, degree in rows:
            p = int(mask)
            if p not in masks or p in pivots or p in targets or int(degree) != p.bit_length()-1:
                raise ValueError(f"invalid or repeated compact target {p}")
            targets.add(p)
    return targets, closure(pivots, targets)


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


def example89():
    n = 89
    order = (1 << n) - 1
    f = modulus(n, (3, 5, 6))
    a = coordinate(f)
    r = polynomial(2)
    anchor = 237608358309219314788467309
    if r.pow_mod(anchor, f) != a:
        raise ArithmeticError("the supplied degree-89 period logarithm failed")
    pivots = read_relations(small_irreducibles(10), n, DATA / "degree-89-period-relations.jsonl")
    powers = recover(pivots, order)
    needed = small_irreducibles(8)
    if not needed <= powers.keys():
        raise ArithmeticError("the degree-89 identities did not cover all requested irreducibles")
    for p in needed:
        v = polynomial(p).compose_mod(a, f)
        if a.pow_mod(powers[p], f) != v or r.pow_mod(anchor*powers[p] % order, f) != v:
            raise ArithmeticError(f"degree-89 exponentiation failed for mask {p}")
    counts = Counter(p.bit_length()-1 for p in needed)
    score = moment_bound(counts, 1024, 30)
    if any(order % d == 0 for d in range(2, 1024)) or score <= n-2:
        raise ArithmeticError("the degree-89 proper-index exclusion failed")
    print(f"Degree 89: {len(pivots)} identities and one supplied logarithm establish "
          f"all {len(needed)} powers through degree eight. Moment score {score} > 87.")
    print("Full order proved for the degree-89 Gauss period and the sparse root.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list-targets", action="store_true", help="emit the target CSV")
    parser.add_argument("--compact", action="store_true", help="check the smaller alternative target list")
    parser.add_argument("--example-89", action="store_true", help="replay the complete one-logarithm example")
    parser.add_argument("--candidate", choices=CANDIDATES, help="sparse modulus used for submitted exponents")
    parser.add_argument("--logs", nargs="+", type=Path, help="verify supplied powers of the sparse root")
    args = parser.parse_args()
    if args.example_89:
        if args.list_targets or args.compact or args.logs or args.candidate:
            parser.error("--example-89 is a standalone certificate")
        example89()
        sys.exit(0)
    if bool(args.logs) != bool(args.candidate) or (args.list_targets and args.logs):
        parser.error("log submissions require a candidate and at least one CSV")
    small = small_irreducibles()
    pivots = read_relations(small)
    raw_count = len(pivots)
    masks = extend_dickson(small, pivots)
    targets, covered = (read_compact_targets if args.compact else select_targets)(masks, pivots)
    counts = Counter(p.bit_length()-1 for p in covered)
    score = moment_bound(counts, INDEX_FLOOR, 129, 3)
    if score <= DEGREE-2:
        raise ArithmeticError("covered degree counts fall short of the character bound")
    if args.list_targets:
        write_targets(targets)
    else:
        with (COMPACT_TARGETS if args.compact else TARGETS).open(newline="") as source:
            rows = list(csv.reader(source))
        if rows != [["mask", "degree"]] + [[str(p), str(p.bit_length()-1)] for p in sorted(targets)]:
            raise ArithmeticError("the published target list differs from reconstruction")
        print(f"{raw_count} listed identities and {len(pivots)-raw_count} further unit pivots verified. "
              f"{len(targets)} inputs imply {len(covered)} polynomial logarithms.")
        print(f"Their conditional moment score is {score} > {DEGREE-2}.")
        if args.logs:
            verify_submissions(args.candidate, args.logs, pivots, masks)
