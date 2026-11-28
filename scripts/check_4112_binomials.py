"""Verify and count the projected binomials in the degree-4112 torsion coordinate."""

import argparse
import csv
import gzip
import json
from concurrent.futures import ProcessPoolExecutor
from math import gcd, prod

from check_4112_descent import DATA, DESCENT, M, TARGET, field_coordinate
from check_projective_4112 import A, B, K, ORDER, Q, ConstantField


TABLE = DATA / "degree-4112-binomial-logs.csv.gz"
POWERS = [pow(3, i, M*M) for i in range(16)]


def orbits(field, unit):
    seen = bytearray(K)
    result = []
    for start in range(1, K):
        if seen[start]:
            continue
        c = start
        orbit = []
        while not seen[c]:
            orbit.append(c)
            seen[c] = 1
            c = field.divide(unit, field.power(c, Q))
        if c != start:
            raise ValueError("invalid binomial Frobenius orbit")
        result.append(orbit)
    return result


def read_rows():
    result = {j: [] for j in POWERS}
    with gzip.open(TABLE, "rt", newline="") as fp:
        reader = csv.DictReader(fp)
        if reader.fieldnames != ["power", "constant", "exponent"]:
            raise ValueError("invalid binomial table header")
        for row in reader:
            j, c, e = (int(row[key]) for key in reader.fieldnames)
            if j not in result or not 0 <= e < B:
                raise ValueError("invalid power or exponent")
            result[j].append((c, e))
    return result


def expand(rows, cycles):
    if [c for c, _ in rows] != [cycle[0] for cycle in cycles]:
        raise ValueError("missing or repeated Frobenius orbit")
    logs = [0]*K  # c=0 gives a torsion element.
    for (_, e), cycle in zip(rows, cycles, strict=True):
        initial = e
        for c in cycle:
            logs[c] = e
            e = Q*e % B
        if e != initial:
            raise ValueError("exponent does not close under Frobenius")
    return logs


def verify_powers(items):
    model = json.loads(DESCENT.read_text())
    f, x, y, embed = field_coordinate(model)
    for j, rows in items:
        coordinate = y.pow_mod(j, f)
        for c, e in rows:
            if (coordinate + embed(c)).pow_mod(A, f) != x.pow_mod(A*e, f):
                raise ValueError(f"incorrect projected power at ({j}, {c})")


def count_orders(tables):
    field = ConstantField()
    unit = json.loads(DESCENT.read_text())["unit"]
    known = prod(json.loads(TARGET.read_text())["known_prime_factors"])
    cofactor = ORDER//known
    if ORDER % known or B % cofactor:
        raise ValueError("incompatible projection orders")
    residues = {(j*(2**i)) % M for j in POWERS for i in range(16)}
    if residues != set(range(1, M)):
        raise ValueError("the sixteen powers fail to cover the nonzero residue classes")
    total_primitive = 0
    full = 0
    for j, rows in tables.items():
        norm_unit = field.power(unit, j)
        logs = expand(rows, orbits(field, norm_unit))
        for c, e in enumerate(logs):
            norm_c = field.power(c, M)
            trivial = c == 0 or norm_c == 1
            if trivial:
                if e % cofactor:
                    raise ValueError("nonzero logarithm in the exceptional class")
            elif gcd(e, cofactor) != 1:
                raise ValueError("proper cofactor order outside the exceptional class")
            else:
                full += 1
            norm = norm_c ^ norm_unit
            if norm == 0:
                raise ValueError("zero element in a nonzero Kummer direction")
            if gcd(e, B) == 1 and gcd(field.log[norm], K-1) == 1:
                total_primitive += 1
    return 16*total_primitive, 16*full


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1, help="number of independent power-check workers")
    parser.add_argument("--rebuild", action="store_true",
                        help="verify by reconstructing the exponents with unit pivots and the previous table")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    tables = read_rows()
    if args.rebuild:
        from solve_4112_binomials import reconstruct
        if tables != reconstruct():
            raise ValueError("reconstructed logarithms differ from the archive")
    else:
        jobs = min(args.jobs, len(tables))
        batches = [list(tables.items())[i::jobs] for i in range(jobs)]
        if jobs == 1:
            verify_powers(batches[0])
        else:
            with ProcessPoolExecutor(jobs) as pool:
                for _ in pool.map(verify_powers, batches):
                    pass
    primitive, full = count_orders(tables)
    count = sum(map(len, tables.values()))
    print(f"Verified {count} binomial logarithms. Among {(M-1)*K:,} distinct elements, "
          f"{primitive:,} are primitive and {full:,} have full projected cofactor order.")


if __name__ == "__main__":
    main()
