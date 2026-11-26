"""Verify degree-halving identities in the binary degree-1229 field."""

import argparse
import gzip
import hashlib
import json
import struct
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
THIRD = DATA / "degree-1229-dyadic-level3.bin.gz"
SAMPLE = DATA / "degree-1229-dyadic-sample.json.gz"
INDEX_BLOCK = struct.Struct("<1029H")


@cache
def first_level():
    with gzip.open(FIRST, "rt") as stream:
        return {int(mask, 16): row for mask, row in json.load(stream).items()}


@cache
def second_level():
    with gzip.open(SECOND, "rt") as stream:
        return {int(p, 16): row for p, row in json.load(stream).items()}


@cache
def third_level():
    """Each degree-16 parent has 1,029 indices in ascending binary degree-eight mask order."""
    with gzip.open(THIRD, "rb") as stream:
        data = stream.read()
    offsets = {p: i*INDEX_BLOCK.size for i, p in enumerate(sorted(second_level()))}
    if (len(data) != len(offsets)*INDEX_BLOCK.size or
            hashlib.sha256(data).hexdigest() != "43d9832c43ac85de67bc4424a603dfd22ad1235f32679d82ec0197a635e81df8"):
        raise ValueError("wrong length or digest for the degree-eight pencil index file")
    return data, offsets


@cache
def sample():
    with gzip.open(SAMPLE, "rt") as stream:
        row = json.load(stream)
    return (int(row["degree16_parent_hex"], 16), int(row["degree8_parent_hex"], 16),
            {int(p, 16): value for p, value in row["pencils"].items()})


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


def native_rows(backend, mode, field_mask, rows):
    lines = [str(field_mask), *(" ".join(map(str, row)) for row in rows)]
    proc = subprocess.run([str(backend.resolve()), mode], input="\n".join(lines)+"\n",
                          text=True, stdout=subprocess.PIPE, check=True)
    return [tuple(map(int, line.split())) for line in proc.stdout.splitlines()]


def native(backend, mode, field_mask, matrices):
    rows = ((mask, *(int(z, 16) for z in matrix)) for mask, matrix in matrices.items())
    return native_rows(backend, mode, field_mask, rows)


def matrix_for(mask):
    if mask in first_level():
        return first_level()[mask]["matrix"]
    if mask in second_level():
        return second_level()[mask][1:]
    return sample()[2][mask][1:]


def indexed_children(backend, field_mask, parent):
    data, offsets = third_level()
    indices = INDEX_BLOCK.unpack_from(data, offsets[parent])
    rows = native(backend, "expand", field_mask, {parent: matrix_for(parent)})
    children = [p for _, p, _, _ in rows]
    if (any(p != parent for p, *_ in rows) or children != sorted(set(children))
            or any(p.bit_length() != 161 for p in children) or not all(indices)):
        raise ArithmeticError("unexpected degree-eight pencil index or parent expansion")
    return dict(zip(children, indices, strict=True))


def verify_octic_group(backend, field_mask, parent):
    indexed = indexed_children(backend, field_mask, parent)
    rows = native_rows(backend, "replay-lines", field_mask, indexed.items())
    if ([p for p, _, _ in rows] != list(indexed)
            or any(degree != 4 or not 1024 <= count <= 1029 for _, count, degree in rows)):
        raise ArithmeticError("incomplete degree-four reduction")
    return list(indexed), sum(count for _, count, _ in rows)


def verify_candidate(name, backend, jobs, field_mask, field, base, table, depth):
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
    if depth == 3:
        third_level()
        def verify_group(parent):
            return verify_octic_group(backend, field_mask, parent)
        distinct = set()
        occurrences = 0
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            for masks, count in pool.map(verify_group, needed):
                distinct.update(masks)
                occurrences += count
        print(f"{name}: verified {len(parents)} degree-32 factors, {len(needed):,} degree-16 factors, "
              f"{len(distinct):,} distinct degree-eight factors and {occurrences:,} finite source "
              f"and cofactor roots of relative degree dividing four, counted before taking binary norms.")
        return
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


def verify_sample(backend, jobs, field_mask, base, field, table, census):
    from check_1229_hermitian_descent import DYADIC_TERMINALS
    from check_1229_log_descent import checked_exponent
    from check_1229_norm_height import norm_quotient, sparse_root

    p16, p8, pencils = sample()
    parents = norm_quotient("product", "pair32", sparse_root("product", field), field)
    if not halve_parents(parents, field).get(p16, 0) % COFACTOR:
        raise ArithmeticError("the sampled branch is absent from the product pentanomial")
    if p8 not in {p for _, p, _, _ in native(backend, "expand", field_mask, {p16: matrix_for(p16)})}:
        raise ArithmeticError("the selected degree-eight factor is absent from its parent")
    children = [p for _, p, _, _ in native(backend, "expand", field_mask, {p8: matrix_for(p8)})]
    if set(children) != pencils.keys() - {p8}:
        raise ArithmeticError("the sample omits a degree-four factor")
    batches = [children[i:i+16] for i in range(0, len(children), 16)]
    def terminals(batch):
        edges = native(backend, "expand", field_mask, {p: matrix_for(p) for p in batch})
        if {p for p, *_ in edges} != set(batch):
            raise ArithmeticError("incomplete terminal expansion")
        return {child for _, child, _, _ in edges}
    masks = set()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        for part in pool.map(terminals, batches):
            masks.update(part)
    solved = {int(row["mask_hex"], 16): int(row["log_mod_C"]) for row in json.loads(DYADIC_TERMINALS.read_text())}
    if solved.keys() - masks or any(p.bit_length()-1 not in (20, 40) for p in masks):
        raise ArithmeticError("unexpected terminal degrees or solved masks outside the sample")
    for p, e in solved.items():
        checked_exponent(p, e, base, field)
    if census:
        quadratic = sorted(p for p in masks if p.bit_length() == 41)
        def smooth(batch):
            proc = subprocess.run([str(backend.resolve()), "terminal"], input="\n".join(map(str, batch))+"\n",
                                  text=True, stdout=subprocess.PIPE, check=True)
            return {int(line.split()[0]) for line in proc.stdout.splitlines()}
        with ThreadPoolExecutor(max_workers=jobs) as pool:
            found = set().union(*pool.map(smooth, [quadratic[i:i+8192] for i in range(0, len(quadratic), 8192)]))
        if found != solved.keys():
            raise ArithmeticError("terminal pencil census differs from the published logarithms")
    print(f"Verified {len(children):,} degree-four factors and {len(masks):,} distinct terminal masks. "
          f"The original table supplies {len(masks & table.keys())} and the quadratic pencils "
          f"supply {len(solved)} exact logarithms.")


def main():
    from check_1229_factor_base_orders import read_table
    from check_1229_log_descent import KNOWN, reduce_task

    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--candidate", choices=("product", "seroussi"), help="verify the descent of one sparse root")
    mode.add_argument("--sample", action="store_true", help="verify the selected product branch down to quadratics")
    mode.add_argument("--parent", type=lambda p: int(p, 0), help="verify or export one factor's children")
    parser.add_argument("--backend", type=Path, required=True, help="compiled degree_1229_dyadic executable")
    parser.add_argument("--jobs", type=int, default=4, help="number of concurrent verification batches")
    parser.add_argument("--depth", type=int, choices=(2, 3), help="verify a candidate to depth 2 or 3, or one degree-16 parent to depth 3")
    parser.add_argument("--child", type=lambda p: int(p, 0), help="expand a degree-eight child of --parent")
    parser.add_argument("--census", action="store_true", help="enumerate the split linear pencils in --sample")
    parser.add_argument("--json", action="store_true", help="export the individual parent task")
    parser.add_argument("--logs", type=Path, help="verify a mask,exponent CSV for the individual parent")
    args = parser.parse_args()
    if args.jobs < 1 or (args.parent is None and (args.json or args.logs)):
        parser.error("use a positive job count; --json and --logs require --parent")
    if args.census and not args.sample:
        parser.error("--census requires --sample")
    if args.depth and not args.candidate:
        if args.depth != 3 or args.parent not in second_level() or args.child is not None or args.json or args.logs:
            parser.error("use --depth with --candidate, or --depth 3 with one degree-16 --parent")
    if args.child is not None and args.parent not in second_level():
        parser.error("--child requires a published degree-16 --parent")
    field_mask, table = read_table()
    field = polynomial(field_mask)
    base = polynomial(2).pow_mod(KNOWN, field)
    if args.candidate:
        verify_candidate(args.candidate, args.backend, args.jobs, field_mask, field, base, table, args.depth or 2)
        return
    if args.sample:
        verify_sample(args.backend, args.jobs, field_mask, base, field, table, args.census)
        return
    p = args.parent
    if args.depth == 3:
        masks, count = verify_octic_group(args.backend, field_mask, p)
        print(f"Verified {len(masks):,} degree-eight pencils and {count:,} finite roots of relative degree dividing four.")
        return
    if args.child is not None:
        indices = indexed_children(args.backend, field_mask, p)
        p = args.child
        if p not in indices:
            parser.error("--child is absent from the degree-16 parent")
        edges = native_rows(args.backend, "expand-lines", field_mask, [(p, indices[p])])
    else:
        if p not in first_level() and p not in second_level() and p not in sample()[2]:
            parser.error("no published pencil for this parent mask")
        edges = native(args.backend, "expand", field_mask, {p: matrix_for(p)})
    if not edges or any(mask != p for mask, *_ in edges):
        raise ArithmeticError("the backend returned a different parent")
    relation = halving_relation(p, (row[1:] for row in edges), field)
    from check_1229_hermitian_descent import records
    from check_1229_log_descent import checked_exponent
    for mask, row in records().items():
        if mask in relation and "log_mod_C" in row:
            table[mask] = checked_exponent(mask, int(row["log_mod_C"]), base, field)
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
