"""Find Gauss period relations from factorizations and affine changes of root-of-unity exponents."""

import argparse
import json
import sys
from collections import Counter
from functools import lru_cache
from pathlib import Path

from check_factor_base import irreducible, polynomial
from find_factor_base_logs import insert
from period_coordinate import frobenius_indices, mask_of


def support_pairs(p, span):
    """Enumerate normalized supports S and qS+b contained in the window [0, span]."""
    for q in range(2, (p-1)//2 + 1):
        inverse = pow(q, -1, p)
        if min(inverse, p-inverse) < q:
            continue
        for anchor in range(span+1):
            offset = -q*anchor % p
            if offset > span:
                continue
            points = [(i, (q*i+offset) % p) for i in range(span+1) if (q*i+offset) % p <= span]
            if len(points) < 3:
                continue
            u, v = points[1]
            if all(u*(j-offset) == (v-offset)*i for i, j in points):
                continue
            left = right = 0
            optional = []
            for i, j in points:
                if i == 0 or i == anchor:
                    left |= 1 << i
                    right |= 1 << j
                else:
                    optional.append((1 << i, 1 << j))
            # Gray code visits each subset with one bit change at a time.
            for step in range(1 << len(optional)):
                if step:
                    a, b = optional[(step & -step).bit_length()-1]
                    left ^= a
                    right ^= b
                if left.bit_count() >= 3:
                    yield q, left, right


def search(n, bound, target_degree, spans, seed):
    p = 2*n+1
    order = (1 << n)-1
    indices = frobenius_indices(n)
    small = [b for b in range(2, 1 << (bound+1)) if irreducible(polynomial(b))]
    wanted = {b for b in small if b < 1 << (target_degree+1)} - {2}
    multipliers = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
    dickson = [0, 2]
    for _ in range(2, max(*spans, *multipliers)+1):
        dickson.append((dickson[-1] << 1) ^ dickson[-2])

    @lru_cache(maxsize=262144)
    def norm_factors(word):
        # N(F) = F(z)F(z^-1), expressed in the variable z+z^-1.
        norm = word.bit_count() % 2
        for j in range(1, word.bit_length()):
            if (word & (word >> j)).bit_count() % 2:
                norm ^= dickson[j]
        factors = polynomial(norm).factor()[1]
        if all(f.degree() <= bound for f, _ in factors):
            return [(mask_of(f), e) for f, e in factors]
        return None

    pivots = {}

    def add(terms, emit=True):
        row = Counter()
        for m, b, e in terms:
            row[b] += e << indices[m]
        if insert(row, pivots, order, fixed_x=False) and emit:
            print(json.dumps(terms, separators=(",", ":")))

    if seed:
        with seed.open() as source:
            for line in source:
                add(json.loads(line), emit=False)
    else:
        for m in multipliers:
            if m % p == 0:
                continue
            for b in small:
                fs = polynomial(b)(polynomial(dickson[m])).factor()[1]
                if all(f.degree() <= bound for f, _ in fs):
                    add([[m % p, b, -1]] + [[1, mask_of(f), e] for f, e in fs])
    for span in spans:
        for q, left, right in support_pairs(p, span):
            ls = norm_factors(left)
            if ls is None:
                continue
            rs = norm_factors(right)
            if rs is not None:
                add([[q, b, -e] for b, e in ls] + [[1, b, e] for b, e in rs])
        free = len(wanted - pivots.keys())
        print(f"Span {span}, {len(pivots)} pivots, {free} further free target columns.", file=sys.stderr)
        if free == 0:
            break


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", type=int)
    parser.add_argument("--factor-degree", required=True, type=int)
    parser.add_argument("--target-degree", type=int, help="stop when these masks depend only on the period")
    parser.add_argument("--spans", nargs="+", required=True, type=int)
    parser.add_argument("--seed", type=Path, help="emit only rows independent of this JSONL file")
    args = parser.parse_args()
    wanted = args.factor_degree if args.target_degree is None else args.target_degree
    if not 1 <= wanted <= args.factor_degree < args.degree or not all(1 <= a < args.degree for a in args.spans):
        parser.error("expected positive factor degrees and support spans below the extension degree")
    search(args.degree, args.factor_degree, wanted, args.spans, args.seed)
