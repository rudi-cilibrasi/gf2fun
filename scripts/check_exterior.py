"""Check the exterior-power criterion on all binary polynomials with constant 1."""

import argparse
from collections import Counter
from itertools import combinations

from make_witnesses import mersenne_factors, primitive


def fixed_dimension(n, taps, k):
    """Nullity of I + wedge^k C, with each matrix column stored as an integer."""
    subsets = [
        sum(1 << i for i in sites)
        for sites in combinations(range(n), k)
    ]
    index = {s: j for j, s in enumerate(subsets)}
    pivots = {}
    high = 1 << (n - 1)
    for j, s in enumerate(subsets):
        column = 1 << j
        shifted = (s & (high - 1)) << 1
        if s & high:
            for target in taps:
                bit = 1 << target
                if shifted & bit == 0:
                    column ^= 1 << index[shifted | bit]
        else:
            column ^= 1 << index[shifted]
        while column:
            pivot = column.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = column
                break
            column ^= pivots[pivot]
    return len(subsets) - len(pivots)


def check_through(limit):
    counts = Counter()
    for n in range(1, limit + 1):
        factors = mersenne_factors(n)
        for lower in range(1, 1 << n, 2):
            taps = [i for i in range(n) if lower & (1 << i)]
            passes = all(fixed_dimension(n, taps, k) == 0 for k in range(1, n // 2 + 1))
            mask = (1 << n) | lower
            if passes != primitive(n, mask, factors):
                raise ValueError(f"criterion disagreement at degree {n}, mask {mask:#x}")
            counts[passes] += 1
    print(f"Checked {sum(counts.values())} polynomials through degree {limit}. "
          f"{counts[True]} are primitive.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int, nargs="?", default=9)
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("the degree limit must be positive")
    check_through(args.limit)
