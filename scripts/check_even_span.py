"""Independently exclude every shorter product tail at the extremal even degree."""

import argparse
import json
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import partial
from pathlib import Path

from flint import fmpz_mod_poly_ctx


DEGREE = 2016
SPAN = 299
ORDER = (1 << DEGREE) - 1


def sieve(supports):
    """Remove supports divisible by a monic binary polynomial of degrees 1 through 10."""
    for g in range(3, 1 << 11, 2):
        high = 1 << (g.bit_length() - 1)
        powers = [1]
        for _ in range(DEGREE):
            x = powers[-1] << 1
            powers.append(x ^ g if x & high else x)
        head = powers[DEGREE] ^ 1
        supports = [(u, v) for u, v in supports if head ^ powers[u+v] ^ powers[u] ^ powers[v]]
    return supports


def exclude(pair, divisors):
    u, v = pair
    x = fmpz_mod_poly_ctx(2).gen()
    f = x**DEGREE + (x**u+1)*(x**v+1)
    if not f.is_irreducible():
        return 0
    for q in divisors:
        if x.pow_mod(ORDER//q, f) == 1:
            return q
    raise ValueError(f"failed to exclude the shorter support {u}, {v}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--factor-table", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("expected at least one verification worker")
    table = json.loads(args.factor_table.read_text())
    divisors = sorted(set(table.get("table2-_data", table)[str(DEGREE)]))
    if not all(q > 1 and ORDER % q == 0 for q in divisors):
        raise ValueError("the proposed proper powers require divisors of the group order")
    supports = [(u, s-u) for s in range(3, SPAN) for u in range(1, (s-1)//2+1)]
    remaining = sieve(supports)
    check = partial(exclude, divisors=divisors)
    if args.jobs == 1:
        reasons = Counter(map(check, remaining))
    else:
        with ProcessPoolExecutor(args.jobs) as pool:
            reasons = Counter(pool.map(check, remaining, chunksize=4))
    reducible = len(supports) - len(remaining) + reasons[0]
    print(f"Degree {DEGREE}: of {len(supports)} product tails below {SPAN}, "
          f"{reducible} are reducible and {len(supports)-reducible} are irreducible of proper order.")
