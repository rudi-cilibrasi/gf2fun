"""Check the endpoint discriminant, the degree-1229 normal census, and the seven-term witness."""

import argparse
import csv
import gzip
from collections import Counter
from pathlib import Path

from flint import fmpz, fmpz_mod_poly_ctx, fmpz_poly

from check_degree_1229 import GROUP, KNOWN, N, PRIMES


DATA = Path(__file__).resolve().parents[1] / "data"


def check_discriminants(through):
    x = fmpz_poly([0, 1])
    binary = fmpz_mod_poly_ctx(2)
    checked = 0
    for n in range(13, through + 1, 4):
        m = (n - 1) // 4
        lift = (x + 1) * (x**m - 1)**4
        for b in range(2, n - 1, 2):
            F = lift - x**b
            expected = (1 + 4*m + 4*(b == 2)) % 8
            if int(F.discriminant()) % 8 != expected:
                raise ArithmeticError(f"discriminant disagrees in degree {n} at {b}")
            unit, factors = binary(F.coeffs()).factor()
            if (unit != 1 or any(e != 1 for _, e in factors)
                    or len(factors) % 2 != (expected == 1)):
                raise ArithmeticError(f"factor parity disagrees in degree {n} at {b}")
            checked += 1
    return checked


def check_factors(x):
    with (DATA / "degree-1229-endpoint-factors.csv").open(newline="") as stream:
        rows = csv.DictReader(stream)
        if rows.fieldnames != ["tap", "factor_mask"]:
            raise ValueError("unexpected factor-table header")
        factors = [(int(row["tap"]), int(row["factor_mask"])) for row in rows]
    if [b for b, _ in factors] != list(range(2, N//2 + 1)):
        raise ValueError("incomplete endpoint factor table")
    base = x**N + x**(N-1) + x + 1
    for b, mask in factors:
        g = x.context()([(mask >> j) & 1 for j in range(mask.bit_length())])
        if mask % 2 == 0 or not 0 < g.degree() < N or (base + x**b) % g != 0:
            raise ArithmeticError(f"invalid proper factor at tap {b}")
        if (base + x**(N-b)) % g.reverse() != 0:
            raise ArithmeticError(f"invalid reciprocal factor at tap {N-b}")


def check_census(shard):
    classes = Counter()
    endpoint_rows = []
    with gzip.open(DATA / "degree-1229-irreducible-supports.csv.gz", "rt", newline="") as stream:
        rows = csv.DictReader(stream)
        if rows.fieldnames != ["a", "b", "c", "missing_mask"]:
            raise ValueError("unexpected support-table header")
        for row in rows:
            a, b, c, missing = map(int, (row[key] for key in rows.fieldnames))
            if a == 1:
                endpoint_rows.append((a, b, c, missing))
            for low, high in ((a == 1, c == N-1), (c == N-1, a == 1)):
                classes[high, low] += 1
                if (low or high) and missing:
                    raise ArithmeticError(f"order projection failed at {a}, {b}, {c}")
    expected = {(False, False): 636760, (True, False): 1203, (False, True): 1203}
    if classes != expected:
        raise ArithmeticError(f"unexpected normal and inverse-normal counts {classes}")
    if shard:
        with shard.open(newline="") as stream:
            rows = csv.reader(stream)
            if next(rows, None) != ["a", "b", "c", "missing_mask"]:
                raise ValueError("expected a --list 1 1 census shard")
            if [tuple(map(int, row)) for row in rows] != endpoint_rows:
                raise ArithmeticError("regenerated endpoint supports differ from the archive")


def main(through, shard):
    if not (fmpz(N).is_prime() and fmpz(307).is_prime() and N-1 == 4*307
            and pow(2, N-1, N) == 1 and all(pow(2, (N-1)//p, N) != 1 for p in (2, 307))):
        raise ArithmeticError("failed multiplicative order of 2 modulo 1229")
    x = fmpz_mod_poly_ctx(2).gen()
    check_factors(x)
    check_census(shard)
    f = x**N + x**(N-1) + x**12 + x**11 + x**8 + x + 1
    if (not f.is_irreducible() or x.pow_mod(GROUP, f) != 1 or x.pow_mod(KNOWN, f) == 1
            or any(x.pow_mod(GROUP//p, f) == 1 for p in PRIMES)):
        raise ArithmeticError("seven-term irreducibility or order test failed")
    total = check_discriminants(through)
    print(f"Verified {total} integral discriminants and binary factorizations through degree {through}.")
    print("Degree 1229: 1226 proper factors, 1203 normal pentanomials, zero with normal inverses.")
    print("Seven terms attain simultaneous normality and pass all five available order projections.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=129, help="largest test degree for the parity formula")
    parser.add_argument("--census-shard", type=Path, help="compare the exact output of census_1229_pentanomials --list 1 1")
    args = parser.parse_args()
    if args.through < 13:
        parser.error("the parity formula starts in degree 13")
    main(args.through, args.census_shard)
