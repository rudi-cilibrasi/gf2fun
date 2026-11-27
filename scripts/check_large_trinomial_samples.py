"""Verify all five-term images from powers through the degree of the published large trinomials."""

import argparse
import csv
import gzip
import json
import sys
from functools import lru_cache
from math import gcd
from pathlib import Path

from check_trinomial_decimations import short_power_support


DATA = Path(__file__).resolve().parents[1] / "data"
SEEDS = DATA / "large-mersenne-trinomial-seeds.json"
WITNESSES = DATA / "large-mersenne-sampled-pentanomials.csv"
HEADER = ("degree", "low", "middle", "high", "seed_tap", "power", "reciprocal")


def vanishes_at_power(support, n, s, m):
    # Reduce F(X^m) by X^n = 1+X^s, keeping only odd coefficients.
    terms = {e*m for e in support}
    while terms and max(terms) >= n:
        reduced = set()
        for e in terms:
            q, r = divmod(e, n)
            j = q
            while True:
                reduced.symmetric_difference_update((r+j*s,))
                if j == 0:
                    break
                j = (j-1) & q
        terms = reduced
    return not terms


def samples(n, taps):
    if n <= 11 or n % 2 == 0 or taps != sorted(set(taps)) or any(not 0 < 2*s < n for s in taps):
        raise ValueError(f"invalid trinomial representatives for degree {n}")
    result = {}
    # The short-power theorem gives these possible odd parts for exponents <= n.
    powers = {7} | {2**h+1 for h in range(1, n.bit_length()) if 2**h+1 <= n}
    for s in taps:
        for power in sorted(powers):
            support = short_power_support((0, s, n), power)
            if support is None or gcd(pow(2, n, power)-1, power) != 1:
                continue
            if len(set(support)) != 5 or not vanishes_at_power(support, n, s, power):
                raise ValueError(f"invalid five-term image in degree {n}, tap {s}, power {power}")
            for reciprocal in (0, 1):
                row = support if not reciprocal else [n-k for k in reversed(support)]
                interior = tuple(row[1:-1])
                if interior in result:
                    raise ValueError(f"repeated five-term image in degree {n}")
                result[interior] = (s, power, reciprocal)
    return [(n, *interior, *result[interior]) for interior in sorted(result)]


def verify_factor_log(path, n, seeds):
    from check_factor_base import polynomial

    x = polynomial(2)

    @lru_cache(maxsize=512)
    def factor_and_power(mask):
        factor = polynomial(mask)
        return factor, x.pow_mod(n, factor)

    count = 0
    positive = []
    with gzip.open(path, "rt") as source:
        for tap, line in enumerate(source, start=1):
            fields = line.split()
            if not fields or int(fields[0]) != tap or tap > n//2:
                raise ValueError("out-of-order or extra tap in the factor certificate")
            count = tap
            if fields[1:] == ["primitive"]:
                positive.append(tap)
                continue
            if len(fields) != 3 or fields[2][0] not in ("p", "q"):
                raise ValueError(f"missing explicit factor at tap {tap}")
            d, mask = int(fields[1]), int(fields[2][1:], 16)
            if not 0 < d < n or mask.bit_length() != d+1:
                raise ValueError(f"invalid factor degree at tap {tap}")
            factor, leading = factor_and_power(mask)
            actual_tap = tap if fields[2][0] == "p" else n-tap
            if leading + x.pow_mod(actual_tap, factor) + 1:
                raise ValueError(f"claimed factor does not divide the trinomial at tap {tap}")
    if count != n//2 or positive != seeds:
        raise ValueError("incomplete factor certificate or inconsistent primitive seeds")
    print(f"Verified a proper factor for all {count-len(seeds):,} excluded reciprocal pairs "
          f"in degree {n}.")


def replay(n, seeds):
    from check_large_circle_orders import mersenne_prime
    from make_packed_mersenne import advance, make_stages

    mersenne_prime(n)
    stages = make_stages(n)
    for s in seeds:
        if advance(1, n, [n, s, 0], stages, n) != 1:
            raise ValueError(f"prime-order power failed for the trinomial with tap {s}")
    print(f"Replayed Lucas–Lehmer and the full polynomial powers of {len(seeds)} "
          f"trinomial representatives in degree {n}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit", action="store_true", help="write the generated witness CSV to stdout")
    parser.add_argument("--replay", type=int, metavar="DEGREE",
                        help="also recheck the Mersenne prime and all positive seeds in one degree")
    parser.add_argument("--factor-log", type=Path,
                        help="also verify every exclusion in the authors' extended gzip certificate for --replay")
    args = parser.parse_args()
    if args.factor_log and args.replay is None:
        parser.error("--factor-log must be paired with --replay")
    if args.emit and args.replay:
        parser.error("choose either CSV output or seed replay")
    seeds = {int(n): taps for n, taps in json.loads(SEEDS.read_text()).items()}
    groups = {n: samples(n, taps) for n, taps in seeds.items()}
    rows = [row for group in groups.values() for row in group]
    if args.emit:
        writer = csv.writer(sys.stdout, lineterminator="\n")
        writer.writerow(HEADER)
        writer.writerows(rows)
        return
    with WITNESSES.open(newline="") as source:
        reader = csv.reader(source)
        if tuple(next(reader)) != HEADER or [tuple(map(int, row)) for row in reader] != rows:
            raise ValueError("the archived witnesses differ from the sampled supports")
    print(f"Verified {len(rows)} five-term supports from the published trinomial lists "
          f"in {sum(bool(group) for group in groups.values())} degrees.")
    counts = ", ".join(f"{n} ({len(group)})" for n, group in groups.items())
    print(f"Degrees with their counts are {counts}.")
    if args.replay is not None:
        if not seeds.get(args.replay):
            parser.error("seed replay requires an archived degree with positive seeds")
        if args.factor_log:
            verify_factor_log(args.factor_log, args.replay, seeds[args.replay])
        replay(args.replay, seeds[args.replay])


if __name__ == "__main__":
    main()
