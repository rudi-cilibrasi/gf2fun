"""Verify polynomial logarithms and bound the index of X without factoring the group order."""

import argparse
import csv
import sys
from collections import Counter
from fractions import Fraction
from itertools import accumulate
from math import prod
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


def moment_bound(counts, index_floor, length, offset=1):
    """Exact rational lower bound for n-2 if the subgroup has index at least index_floor."""
    # The real weights are w[i] / sqrt(2) for odd i and w[i] for even i.
    w = [(i + offset) * (length + offset - i) * (7 if i % 2 else 5) for i in range(length + 1)]
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

def seroussi_relations(logs, f):
    """Complete any single missing log in two low-degree relations for Seroussi's field."""
    x = polynomial(2)
    tail = x**15 + x**6 + x**2 + 1
    left = (3, 7, 6031, 7741, 8191)
    right = (47, 16197, 121583)
    if (polynomial(3) * polynomial(32707) != tail
            or prod(map(polynomial, left)) != x**39 + 1
            or prod(map(polynomial, right)) != x**19 * tail + 1):
        raise ArithmeticError("incorrect factorizations for the degree-1229 relations")
    if not all(irreducible(polynomial(p)) for p in {*left, *right, 32707}):
        raise ArithmeticError("a listed polynomial factor is reducible")
    ratios = {p: 32 for p in left}
    ratios.update({p: -1 for p in right})
    relations = (({3: 1, 32707: 1}, 1229), (ratios, 0))
    order = (1 << 1229) - 1
    added = 0
    while True:
        before = len(logs)
        for terms, target in relations:
            missing = terms.keys() - logs.keys()
            if len(missing) != 1:
                continue
            p = missing.pop()
            rest = sum(c * logs[q] for q, c in terms.items() if q != p)
            exponent = ((target - rest) * pow(terms[p], -1, order)) % order
            if not irreducible(polynomial(p)) or x.pow_mod(exponent, f) != polynomial(p):
                raise ArithmeticError("the derived polynomial logarithm failed direct verification")
            logs[p] = exponent
            added += 1
        if len(logs) == before:
            return added


def list_targets(seroussi):
    """Emit one deterministic choice of the new logs in the extended-index certificate."""
    implied = {2, 32707, 121583} if seroussi else {2}
    needed = 275 if seroussi else 276
    writer = csv.writer(sys.stdout, lineterminator="\n")
    writer.writerow(("mask", "degree"))
    for degree in range(1, 17):
        for mask in range(1 << degree, 1 << (degree+1)):
            if mask in implied or not irreducible(polynomial(mask)):
                continue
            writer.writerow((mask, degree))
            if degree == 16:
                needed -= 1
                if needed == 0:
                    return
    raise ArithmeticError("insufficient degree-16 irreducibles")


def check(n, paths, extended_index=False, seroussi=False):
    taps, index_floor, length = CASES[n]
    if seroussi:
        taps = (2, 6, 15)
    f = modulus(n, taps)
    offset = 1
    if n == 1229:
        from check_degree_1229 import check as check_partial_order
        check_partial_order(index_floor - 1, taps)
        target = irreducible_counts(15)
        target[16] = 958
        if extended_index:
            from batch_degree_1229 import verify_published
            index_floor = verify_published() + 1
            length, offset, target[16] = 129, 3, 276
        target_score = moment_bound(target, index_floor, length, offset)
        if target_score <= n - 2:
            raise ArithmeticError("the proposed degree-1229 target is insufficient")
        print(f"Degree 1229 target: {sum(target.values())} polynomial values, "
              f"certified threshold {target_score} > {n-2}.")
    elif any(((1 << n) - 1) % d == 0 for d in range(2, index_floor)):
        raise ArithmeticError("small divisor invalidates the index floor")
    if not irreducible(f):
        raise ValueError("the field modulus is reducible")
    logs = verify_logs(paths, n, f)
    if seroussi:
        derived = seroussi_relations(logs, f)
        print(f"Additional logarithms from the two polynomial relations: {derived}.")
    counts = Counter(mask.bit_length() - 1 for mask in logs)
    size = ratio_bound(n, counts)
    index_ceiling = ((1 << n) - 1) // size
    score = moment_bound(counts, index_floor, length, offset)
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
    parser.add_argument("--extended-index", action="store_true", help="replay the larger degree-1229 divisor bound")
    parser.add_argument("--seroussi", action="store_true", help="use the degree-1229 taps 2, 6, 15")
    parser.add_argument("--list-targets", action="store_true", help="write the degree-1229 target masks as CSV")
    args = parser.parse_args()
    if args.list_targets:
        if args.degree != 1229 or args.logs or args.extended_index:
            parser.error("list targets for degree 1229 with an optional --seroussi")
        list_targets(args.seroussi)
        sys.exit(0)
    if (args.extended_index or args.seroussi) and args.degree != 1229:
        parser.error("the alternate modulus and extended index apply to degree 1229")
    paths = args.logs or []
    if not paths and args.degree != 1229:
        paths = [DATA / f"factor-base-{args.degree}.csv"]
    if not check(args.degree, paths, args.extended_index, args.seroussi) and args.logs is None and args.degree != 1229:
        raise SystemExit("the published certificate is incomplete")
