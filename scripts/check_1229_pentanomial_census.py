"""Audit all degree-1229 support and sieve counts, and verify each exceptional order projection with FLINT."""

import argparse
import csv
from collections import Counter
from math import comb
from pathlib import Path

from flint import fmpz_mod_poly_ctx

from check_degree_1229 import GROUP, KNOWN, N, PRIMES
from check_factor_base import DATA


CENSUS = DATA/"degree-1229-pentanomial-census.csv"
EXCEPTIONS = DATA/"degree-1229-order-exceptions.csv"
PACKED_COLUMNS = ("smallest_tap", "supports", "no_small_factor", "irreducibles", "all_five",
                  "missing_p1", "missing_p2", "missing_both", "other")
POWER_COLUMNS = ("smallest_tap", "supports", "power_tests", "divisors")


def sieve_tables():
    binary = fmpz_mod_poly_ctx(2)
    tables = []
    for d in range(2, 11):
        for mask in range((1 << d)+1, 2 << d, 2):
            g = binary([(mask >> j) & 1 for j in range(d+1)])
            if not g.is_irreducible():
                continue
            powers, places = [], [0]*(1 << d)
            r = 1
            for j in range(N+1):
                powers.append(r)
                places[r] |= 1 << j
                r *= 2
                if r >= 1 << d:
                    r ^= mask
            tables.append((powers, places))
    if len(tables) != 224:
        raise ArithmeticError("incomplete small-factor sieve")
    return tables


def sieve_count(a, tables):
    """Count equal endpoint gaps with weight one half, independently of the C++ tie rule."""
    right = N-a
    interior = (1 << right)-1
    endpoint = 1 << right
    lists = [(powers, places, 1 ^ powers[a] ^ powers[N]) for powers, places in tables]
    strict = tied = 0
    for b in range(a+1, right):
        excluded = 0
        for powers, places, residue in lists:
            excluded |= places[residue ^ powers[b]]
        strict += ((~excluded & interior) >> (b+1)).bit_count()
        tied += int(not (excluded & endpoint))
    if tied % 2:
        raise ArithmeticError("unpaired reflected supports at an endpoint tie")
    return strict + tied//2


def verify_exceptions():
    binary = fmpz_mod_poly_ctx(2)
    x = binary.gen()
    counts = Counter()
    previous = (0, 0, 0)
    exponents = [GROUP//p for p in PRIMES] + [KNOWN]
    with EXCEPTIONS.open(newline="") as stream:
        reader = csv.reader(stream)
        if next(reader, []) != ["a", "b", "c", "missing_mask"]:
            raise ValueError("invalid exception table header")
        for row in reader:
            a, b, c, missing = map(int, row)
            if (not 0 < a < b < c < N or (a, b, c) >= (N-c, N-b, N-a)
                    or (a, b, c) <= previous or not 0 < missing < 32):
                raise ValueError(f"invalid exception row {row}")
            previous = (a, b, c)
            f = x**N + x**a + x**b + x**c + 1
            if not f.is_irreducible():
                raise ArithmeticError(f"reducible exception {row}")
            bits = sum(1 << j for j, e in enumerate(exponents) if x.pow_mod(e, f) == 1)
            if bits != missing:
                raise ArithmeticError(f"incorrect order projections at {row}")
            counts[a, missing] += 1
    return counts


def compare_shard(path, rows):
    with path.open(newline="") as stream:
        reader = csv.reader(stream)
        header = tuple(next(reader, []))
        if header == PACKED_COLUMNS:
            keys = header
        elif header == POWER_COLUMNS:
            keys = ("smallest_tap", "supports", "no_small_factor", "divides_known_part")
        else:
            raise ValueError(f"unrecognized shard columns in {path}")
        seen = set()
        for values in reader:
            a = int(values[0])
            if a not in rows or a in seen or tuple(map(int, values)) != tuple(rows[a][k] for k in keys):
                raise ArithmeticError(f"shard disagreement at tap {a} in {path}")
            seen.add(a)
        if not seen:
            raise ValueError(f"empty shard in {path}")


def audit(shards):
    exceptions = verify_exceptions()
    tables = sieve_tables()
    counts = Counter()
    rows = {}
    with CENSUS.open(newline="") as stream:
        reader = csv.DictReader(stream)
        if tuple(reader.fieldnames) != (*PACKED_COLUMNS, "divides_known_part"):
            raise ValueError("invalid census header")
        for a, strings in enumerate(reader, 1):
            row = {k: int(v) for k, v in strings.items()}
            if (a > N//2 or row["smallest_tap"] != a or min(row.values()) < 0
                    or row["supports"] != 2*(N//2-a)**2
                    or row["no_small_factor"] != sieve_count(a, tables)
                    or row["irreducibles"] > row["no_small_factor"]):
                raise ArithmeticError(f"support or sieve count failed at tap {a}")
            missing = [exceptions[a, flags] for flags in range(32)]
            if ((row["missing_p1"], row["missing_p2"], row["missing_both"]) != tuple(missing[1:4])
                    or row["other"] != sum(missing[4:])
                    or row["all_five"] + sum(missing) != row["irreducibles"]
                    or sum(missing[16:]) != row["divides_known_part"]):
                raise ArithmeticError(f"projection counts disagree at tap {a}")
            rows[a] = row
            counts.update(row)
    if len(rows) != N//2 or 2*counts["supports"] != comb(N-1, 3):
        raise ArithmeticError("incomplete reciprocal coverage")
    for path in shards:
        compare_shard(path, rows)
    print(f'{counts["supports"]:,} reciprocal pairs, {counts["no_small_factor"]:,} sieve survivors, '
          f'{counts["irreducibles"]:,} irreducibles, {sum(exceptions.values())} verified exceptions.')


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shards", nargs="*", type=Path, default=(),
                        help="also compare output from either C++ search")
    audit(parser.parse_args().shards)
