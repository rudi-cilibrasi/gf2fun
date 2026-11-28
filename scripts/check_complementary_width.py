"""Check normalized tap bounds and the degrees attaining the sharp bound."""

import argparse
import csv
import json
from collections import Counter
from math import gcd
from pathlib import Path

from check_complementary_taps import order_obstructions


DATA = Path(__file__).resolve().parents[1] / "data"


def width(n, b, a):
    """The best K using either complementary tap and either reciprocal."""
    return min((s + max(s, t)) // gcd(s, t)
               for s in (b, n - b) for t in (a, n - a))


def check_table(path, degrees):
    high = []
    counts = Counter()
    with path.open(newline="") as source:
        rows = csv.reader(source)
        if next(rows) != ["degree", "b", "a"]:
            raise ValueError(f"unexpected header in {path}")
        for n, row in zip(degrees, rows, strict=True):
            degree, b, a = map(int, row)
            if degree != n or not 0 < 2*b < n or not 0 < 2*a <= n or a == b or gcd(n, a, b) != 1:
                raise ValueError(f"invalid support for degree {n}")
            k = width(n, b, a)
            counts[k] += 1
            if k >= 18:
                high.append((n, k))
    return counts, high


def check_sharpness(n, gp):
    # Read the shape in all four orientations, including the n/2 singleton.
    pairs = [(b, a) for b in range(1, (n + 1)//2) for a in range(1, n//2 + 1)
             if a != b and gcd(n, a, b) == 1 and width(n, b, a) < 18]
    failures = order_obstructions(n, pairs, gp)
    print(f"Degree {n} has {len(pairs)} reciprocal classes below 18. "
          f"All {sum(failures.values())} irreducibles have proper order. "
          f"Obstruction counts by divisor: {dict(sorted(failures.items()))}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sharpness", action="store_true",
                        help="exhaust all smaller supports in the extremal degrees with PARI and FLINT")
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    args = parser.parse_args()
    counts = Counter()
    high = []
    for start, end, step in ((5, 1228, 1), (1230, 2292, 2)):
        part, extrema = check_table(DATA / f"complementary-width-{start}-{end}.csv",
                                    range(start, end + 1, step))
        counts.update(part)
        high.extend(extrema)
    if high != [(1320, 18), (1380, 18)] or sum(counts.values()) != 1756:
        raise ArithmeticError("unexpected extremal witnesses")
    print(f"The 1,756 witnesses have normalized widths {dict(sorted(counts.items()))}.")
    with (DATA / "mersenne-complementary-width-extra.json").open() as source:
        extra_degrees = sorted(map(int, json.load(source)))
    extra, extrema = check_table(DATA / "complementary-width-extra.csv", extra_degrees)
    if extrema != [(3696, 18)]:
        raise ArithmeticError("unexpected extremal witness in the additional degrees")
    print(f"The {len(extra_degrees)} additional witnesses have widths {dict(sorted(extra.items()))}.")
    if args.sharpness:
        for n, _ in high + extrema:
            check_sharpness(n, args.gp)


if __name__ == "__main__":
    main()
