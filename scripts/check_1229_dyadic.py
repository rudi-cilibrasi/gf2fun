"""Verify degree-halving identities in the binary degree-1229 field."""

import argparse
import gzip
import json
import subprocess
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from functools import cache
from pathlib import Path

from check_1229_isogeny_logs import H1, Q
from check_degree_1229 import COFACTOR
from check_factor_base import DATA, polynomial


FIRST = DATA / "degree-1229-dyadic-level1.json.gz"
SECOND = DATA / "degree-1229-dyadic-level2.json.gz"


@cache
def first_level():
    with gzip.open(FIRST, "rt") as stream:
        return {int(mask, 16): row for mask, row in json.load(stream).items()}


@cache
def second_level():
    with gzip.open(SECOND, "rt") as stream:
        return {int(p, 16): row for p, row in json.load(stream).items()}


def halving_relation(mask, edges, field):
    """Verify the unprojected norm identity before extracting its logarithmic coefficients."""
    degree = mask.bit_length() - 1
    m = degree // 2
    if degree % 40:
        raise ValueError("the binary target degree must be divisible by 40")
    source = residual = polynomial(1)
    relation = Counter({2: m, 3: 2*m})  # h1 = T(T+1)^2
    inverse = pow(Q, -1, COFACTOR)
    seen = set()
    for child, left, right in edges:
        d = child.bit_length() - 1
        if child in seen or d <= 0 or m % d or min(left, right) < 0 or not (left or right):
            raise ValueError("invalid child in a degree-halving certificate")
        seen.add(child)
        p = polynomial(child)
        if left:
            source = source * (p if left == 1 else p.pow_mod(left, field)) % field
        if right:
            residual = residual * (p if right == 1 else p.pow_mod(right, field)) % field
        relation[child] += inverse * left - right
    actual = (polynomial(mask) * residual % field).pow_mod(Q, field)
    expected = H1.pow_mod(m*Q, field) * source % field
    if actual != expected:
        raise ArithmeticError(f"the unprojected degree-halving identity failed at {mask:#x}")
    return relation


def halve_parents(relation, field):
    result = Counter()
    rows = first_level()
    for mask, weight in relation.items():
        edges = ((int(p, 16), a, b) for p, a, b in rows[mask]["children"])
        children = halving_relation(mask, edges, field)
        result.update({p: weight * e for p, e in children.items()})
    return result


def native(backend, mode, field_mask, matrices):
    lines = [str(field_mask)]
    for mask, matrix in matrices.items():
        lines.append(" ".join(map(str, (mask, *(int(z, 16) for z in matrix)))))
    proc = subprocess.run([str(backend.resolve()), mode], input="\n".join(lines)+"\n",
                          text=True, stdout=subprocess.PIPE, check=True)
    return [tuple(map(int, line.split())) for line in proc.stdout.splitlines()]


def matrix_for(mask):
    if mask in first_level():
        return first_level()[mask]["matrix"]
    return second_level()[mask][1:]


def verify_candidate(name, backend, jobs, field_mask, field, base, table):
    from check_1229_log_descent import reduce_task
    from check_1229_norm_height import norm_quotient, sparse_root

    root = sparse_root(name, field)
    parents = norm_quotient(name, "pair32", root, field)
    for p in parents:
        recorded = [(p, int(child, 16), a, b) for child, a, b in first_level()[p]["children"]]
        if native(backend, "expand", field_mask, {p: matrix_for(p)}) != recorded:
            raise ArithmeticError("regenerated and published first-level factors differ")
    first = reduce_task(name, root, halve_parents(parents, field), table, base, field, None)
    needed = [int(row["mask_hex"], 16) for row in first["remaining"]]
    batches = [needed[i:i+64] for i in range(0, len(needed), 64)]
    def verify(batch):
        return native(backend, "verify", field_mask, {p: matrix_for(p) for p in batch})
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        rows = [row for batch in pool.map(verify, batches) for row in batch]
    if [p for p, _, _ in rows] != needed or any(count <= 0 or degree > 8 for _, count, degree in rows):
        raise ArithmeticError("incomplete second-level certificate")
    print(f"{name}: verified {len(parents)} degree-32 factors, {len(needed):,} degree-16 factors "
          f"and {sum(count for _, count, _ in rows):,} child occurrences, "
          f"maximum relative degree {max(degree for _, _, degree in rows)}.")


def main():
    from check_1229_factor_base_orders import read_table
    from check_1229_log_descent import KNOWN, reduce_task

    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--candidate", choices=("product", "seroussi"), help="replay both levels for one root")
    mode.add_argument("--parent", type=lambda p: int(p, 0), help="verify or export one factor's children")
    parser.add_argument("--backend", type=Path, required=True, help="compiled degree_1229_dyadic executable")
    parser.add_argument("--jobs", type=int, default=4, help="concurrent second-level verification batches")
    parser.add_argument("--json", action="store_true", help="export the individual parent task")
    parser.add_argument("--logs", type=Path, help="verify a mask,exponent CSV for the individual parent")
    args = parser.parse_args()
    if args.jobs < 1 or (args.candidate and (args.json or args.logs)):
        parser.error("use a positive job count; --json and --logs require --parent")
    field_mask, table = read_table()
    field = polynomial(field_mask)
    base = polynomial(2).pow_mod(KNOWN, field)
    if args.candidate:
        verify_candidate(args.candidate, args.backend, args.jobs, field_mask, field, base, table)
        return
    p = args.parent
    if p not in first_level() and p not in second_level():
        parser.error("no published pencil for this parent mask")
    edges = native(args.backend, "expand", field_mask, {p: matrix_for(p)})
    if not edges or any(mask != p for mask, *_ in edges):
        raise ArithmeticError("the backend returned a different parent")
    relation = halving_relation(p, (row[1:] for row in edges), field)
    task = reduce_task(f"dyadic-{p:#x}", polynomial(p), relation, table, base, field, args.logs)
    if args.json:
        print(json.dumps(task, indent=2))
    elif task["remaining"]:
        print(f"Verified {len(task['remaining'])} remaining logarithms of maximum relative degree "
              f"{max(r['relative_degree'] for r in task['remaining'])}.")
    else:
        print(f"Verified projected logarithm {task['known_exponent_mod_C']}.")


if __name__ == "__main__":
    main()
