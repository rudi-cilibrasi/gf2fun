"""Verify polynomial logarithms and bound the index of X without factoring the group order."""

import argparse
import csv
from collections import Counter
from fractions import Fraction
from itertools import accumulate
from pathlib import Path

from flint import nmod_poly


DATA = Path(__file__).resolve().parents[1] / "data"
# Interior exponents, lower bound for a proper index, length of the character sum.
CASES = {47: ((1, 4, 5), 176, 22), 61: ((1, 2, 5), 1024, 28),
         89: ((3, 5, 6), 1024, 30), 1229: ((27, 50, 77), 10**10 + 1, 84)}


def polynomial(mask):
    return nmod_poly([(mask >> i) & 1 for i in range(mask.bit_length())], 2)


def modulus(n, taps):
    return polynomial((1 << n) + sum(1 << i for i in taps) + 1)


def irreducible(f):
    return f.degree() > 0 and f.factor()[1] == [(f, 1)]


def irreducible_counts(limit):
    counts = {}
    for d in range(1, limit + 1):
        lower = sum(e * count for e, count in counts.items() if d % e == 0)
        counts[d] = ((1 << d) - lower) // d
    return counts


def ratio_bound(n, counts):
    """Count reduced smooth fractions with numerator and denominator degree sum below n."""
    a = (n - 1) // 2
    b = n - 1 - a
    smooth = [1] + [0] * b
    inverse = smooth.copy()
    for degree, count in counts.items():
        for _ in range(count):
            for j in range(degree, b + 1):
                smooth[j] += smooth[j - degree]
            for j in range(b, degree - 1, -1):
                inverse[j] -= inverse[j - degree]
    prefix = list(accumulate(smooth))
    return sum(inverse[j] * prefix[a-j] * prefix[b-j] for j in range(a + 1))


def moment_bound(counts, index_floor, length):
    """Exact rational lower bound for n-2 if the subgroup has index at least index_floor."""
    # The real weights are w[i] / sqrt(2) for odd i and w[i] for even i.
    w = [(i + 1) * (length + 1 - i) * (7 if i % 2 else 5) for i in range(length + 1)]
    norm = sum(Fraction(v*v, 1 << (i % 2)) for i, v in enumerate(w))
    total = 0
    for k in range(1, length + 1):
        known = sum(d * count for d, count in counts.items() if k % d == 0)
        moment = 1 + known - Fraction((1 << k) - known, index_floor - 1)
        # w[i]*w[i+k] times the three powers of 1/sqrt(2) has an integer exponent of 1/2.
        cross = sum(Fraction(w[i] * w[i+k], 1 << ((k + i % 2 + (i+k) % 2) // 2))
                    for i in range(length + 1 - k))
        total += 2 * cross * moment
    return total / norm


def verify_logs(paths, n, f):
    x = polynomial(2)
    logs = {2: 1}
    for path in paths:
        seen = set()
        with path.open(newline="") as source:
            reader = csv.DictReader(source)
            if reader.fieldnames != ["mask", "exponent"]:
                raise ValueError("expected the CSV columns mask,exponent")
            for row in reader:
                mask, exponent = int(row["mask"]), int(row["exponent"])
                if not 2 <= mask < 1 << n or not 0 <= exponent < (1 << n) - 1:
                    raise ValueError(f"out-of-range polynomial or exponent in {path}")
                if mask in seen or None in row:
                    raise ValueError(f"invalid or repeated row for mask {mask} in {path}")
                seen.add(mask)
                if logs.get(mask) == exponent:
                    continue
                p = polynomial(mask)
                if not irreducible(p) or x.pow_mod(exponent, f) != p:
                    raise ValueError(f"unverified irreducible or logarithm for mask {mask}")
                logs[mask] = exponent
    return logs

def check(n, paths):
    taps, index_floor, length = CASES[n]
    f = modulus(n, taps)
    if n == 1229:
        from check_degree_1229 import check as check_partial_order
        check_partial_order(index_floor - 1)
        target = irreducible_counts(15)
        target[16] = 958
        target_score = moment_bound(target, index_floor, length)
        if target_score <= n - 2:
            raise ArithmeticError("the proposed degree-1229 target is insufficient")
        print(f"Degree 1229 target: {sum(target.values())} polynomial values, "
              f"certified threshold {target_score} > {n-2}.")
    elif any(((1 << n) - 1) % d == 0 for d in range(2, index_floor)):
        raise ArithmeticError("small divisor invalidates the index floor")
    if not irreducible(f):
        raise ValueError("the field modulus is reducible")
    logs = verify_logs(paths, n, f)
    counts = Counter(mask.bit_length() - 1 for mask in logs)
    size = ratio_bound(n, counts)
    index_ceiling = ((1 << n) - 1) // size
    score = moment_bound(counts, index_floor, length)
    print(f"Verified polynomial logarithms in degree {n}: {len(logs)}.")
    print(f"Distinct reduced fractions: {size}. Index at most {index_ceiling}.")
    print(f"Character sum: {score}. A proper subgroup requires it to be at most {n-2}.")
    full = index_ceiling < index_floor or score > n - 2
    print("Full multiplicative order proved." if full else "Partial certificate. Full order remains open.")
    return full


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", type=int, choices=sorted(CASES))
    parser.add_argument("--logs", nargs="+", action="extend", type=Path, help="one or more logarithm CSVs")
    args = parser.parse_args()
    paths = args.logs or []
    if not paths and args.degree != 1229:
        paths = [DATA / f"factor-base-{args.degree}.csv"]
    if not check(args.degree, paths) and args.logs is None and args.degree != 1229:
        raise SystemExit("the published certificate is incomplete")
