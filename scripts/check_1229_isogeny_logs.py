"""Derive projected logarithms by pulling back the degree-1229 table through its rational map."""

import argparse
import csv
import subprocess
from collections import Counter
from functools import lru_cache
from pathlib import Path

from check_1229_factor_base_orders import read_table
from check_degree_1229 import COFACTOR, PRIMES
from check_factor_base import polynomial
from period_coordinate import mask_of


Q = 1024
H0 = polynomial(37)
H1 = polynomial(10)


@lru_cache(None)
def homogeneous_monomials(degree):
    """Binary masks of h0^i h1^(degree-i) for homogeneous substitution."""
    return tuple(mask_of(H0**i * H1**(degree-i)) for i in range(degree+1))


def pullback(mask):
    value = 0
    monomials = homogeneous_monomials(mask.bit_length()-1)
    while mask:
        bit = mask & -mask
        value ^= monomials[bit.bit_length()-1]
        mask ^= bit
    return value


def mobius(n):
    sign = 1
    p = 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            sign = -sign
        p += 1
    return -sign if n > 1 else sign


def irreducible_fibers(m):
    """Count exact-degree m binary prime polynomials with irreducible quintic pullback."""
    traces = [2, -2]
    for d in range(2, m+1):
        traces.append(-2*traces[d-1]-2*traces[d-2])
    total = sum(mobius(m//d) * (2**d+1-traces[d]) for d in range(1, m+1)
                if m % d == 0 and (m//d) % 5)
    count, remainder = divmod(2*total, 5*m)
    if remainder:
        raise ArithmeticError("nonintegral elliptic fiber count")
    return count


def derive(frontier, logs):
    inverse = pow(Q, -1, COFACTOR)
    denominator_log = logs[2] + 2*logs[3]
    result = {}
    counts = Counter()
    t = polynomial(2)
    for p, e in frontier.items():
        d = p.bit_length()-1
        target = pullback(p)
        u = polynomial(target)
        # Every reducible fiber of this isogeny has a rational point over F_(2^d).
        if u.gcd(t.pow_mod(1 << d, u) + t) != 1:
            continue
        counts[d] += 1
        new_log = (e*inverse + d*denominator_log) % COFACTOR
        if target in logs:
            if logs[target] != new_log:
                raise ArithmeticError("the pullback disagrees with the original table")
        elif target in result:
            raise ArithmeticError("two distinct irreducibles gave one pullback")
        else:
            result[target] = new_log
    return result, counts


def verify_powers(executable, modulus_mask, logs):
    header = " ".join(map(str, (modulus_mask, *PRIMES)))
    rows = (f"{p} {e}" for p, e in sorted(logs.items()))
    source = "\n".join([header, *rows]) + "\n"
    subprocess.run([str(executable.resolve()), "--projected"], input=source, text=True, check=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--export", type=Path, help="write new mask,exponent rows in decimal")
    parser.add_argument("--second-step", action="store_true", help="also pull back the new irreducibles once")
    parser.add_argument("--verify-powers", metavar="NTL_EXECUTABLE", type=Path,
                        help="independently check every projected identity in the model field")
    args = parser.parse_args()
    modulus_mask, table = read_table()
    new_logs, fibers = derive(table, table)
    for d in {p.bit_length()-1 for p in table}:
        if fibers[d] != irreducible_fibers(d):
            raise ArithmeticError(f"the degree-{d} fiber count disagrees with the isogeny")
    if args.second_step:
        second, _ = derive(new_logs, table | new_logs)
        new_logs.update(second)
    counts = Counter(m.bit_length()-1 for m in new_logs)
    print(f"Derived {len(new_logs):,} new projected logarithms. Counts by degree: {dict(sorted(counts.items()))}.", flush=True)
    if args.verify_powers:
        verify_powers(args.verify_powers, modulus_mask, new_logs)
    if args.export:
        with args.export.open("w", newline="") as stream:
            writer = csv.writer(stream, lineterminator="\n")
            writer.writerow(("mask", "exponent"))
            writer.writerows(sorted(new_logs.items()))
