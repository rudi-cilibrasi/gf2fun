"""Classify binary trinomials and pentanomials of root order at most 16 times their degree."""

import argparse
from itertools import combinations
from math import gcd, lcm

from flint import fmpz, fmpz_poly

from check_cubed_parity import BINARY, X, polynomial
from check_sparse_circuit_orders import binary_degree
from check_sparse_root_orders import cyclotomic_census
from check_trinomial_subfield_pairs import prime_divisors


# Root order: (normalized degree, interior exponents up to reciprocation).
BASES = {
    3: (2, [(1,)]), 5: (4, [(1, 2, 3)]), 7: (3, [(1,)]), 15: (4, [(1,)]),
    17: (8, [(3, 4, 5)]), 21: (6, [(1, 2, 4)]),
    31: (5, [(2,), (1, 2, 3), (1, 2, 4)]), 33: (10, [(1, 5, 9), (3, 5, 7)]),
    51: (8, [(1, 3, 4)]), 63: (6, [(1,), (1, 2, 5), (1, 3, 4)]),
    73: (9, [(1,), (1, 2, 4), (1, 3, 6), (2, 5, 6)]), 85: (8, [(1, 3, 7)]),
    89: (11, [(1, 6, 7)]), 91: (12, [(1, 9, 10)]), 93: (10, [(1, 3, 8), (2, 4, 5)]),
    129: (14, [(5, 7, 9)]), 219: (18, [(1, 2, 10)]),
}


def reflection(n, taps):
    return tuple(n - t for t in reversed(taps))


def covers_unit_cosets(n, r, count):
    """Test whether the odd prefix representatives of each doubling coset have gcd one."""
    labels = bytearray(r)
    common = [0]
    covered = 0
    for j in range(1, (n-1)//2 + 1, 2):
        if gcd(j, r) != 1:
            continue
        label = labels[j]
        if not label:
            label = len(common)
            common.append(0)
            k = j
            while not labels[k]:
                labels[k] = label
                k = 2*k % r
        if common[label] != 1:
            common[label] = gcd(common[label], j)
            if common[label] == 1:
                covered += 1
                if covered == count:
                    return True
    return False


def candidate_orders():
    # For a normalized support, r <= 16*n and 5*n^4 <= 16*r^3 give this cutoff.
    bound = 16**5 // 5
    degrees = [0]*(bound+1)
    degrees[1] = 1
    cases = []
    normalized = 0
    for r in range(3, bound+1, 2):
        n = degrees[r] = binary_degree(r)
        if r > 16*n or 5*n**4 > 16*r**3:
            continue
        if any(n == p*degrees[r//p] for p in prime_divisors(r)):
            continue
        normalized += 1
        count = int(fmpz(r).euler_phi())//n
        if count == 1:
            # The normalized full unit group must have prime modulus. Its factor is 1+...+X^(r-1).
            if not fmpz(r).is_prime():
                raise ArithmeticError(f"unexpected normalized full orbit at {r}")
            if r > 5:
                continue
        elif covers_unit_cosets(n, r, count):
            continue
        cases.append((n, r))
    if normalized != 4760 or len(cases) != 206:
        raise ArithmeticError(f"unexpected order sieve counts: {normalized}, {len(cases)}")
    return cases


def flint_census(cases):
    """Factor each binary cyclotomic polynomial and compare every sparse support."""
    found = {}
    for n, r in cases:
        phi = BINARY([int(c) % 2 for c in fmpz_poly.cyclotomic(r)])
        unit, factors = phi.factor()
        product = BINARY([int(unit)])
        sparse = set()
        for f, multiplicity in factors:
            if multiplicity != 1 or f.degree() != n:
                raise ArithmeticError(f"wrong factor degree or multiplicity at {r}")
            product *= f
            support = tuple(i for i, c in enumerate(f) if c)
            if len(support) <= 5:
                sparse.add(support[1:-1])
        if product != phi:
            raise ArithmeticError(f"incomplete factorization at {r}")
        if sparse:
            found[n, r] = sparse
    return found


def verified_bases():
    found = {}
    for r, (n, representatives) in BASES.items():
        taps = set()
        for row in representatives:
            reverse = reflection(n, row)
            if row > reverse or row in taps or gcd(n, *row) != 1:
                raise ArithmeticError(f"invalid normalized representative at {r}")
            taps.update((row, reverse))
        for row in taps:
            f = polynomial((0, *row, n))
            if (not f.is_irreducible() or X.pow_mod(r, f) != 1 or
                    any(X.pow_mod(r//p, f) == 1 for p in prime_divisors(r))):
                raise ArithmeticError(f"incorrect order at {n}, {row}")
        found[n, r] = taps
    return found


def members(n):
    """Yield (root order, canonical taps) in a given degree without factoring that degree."""
    for r, (m, rows) in BASES.items():
        scale, remainder = divmod(n, m)
        if remainder or not scale:
            continue
        residual = scale
        for p in prime_divisors(r):
            if ((1 << m)-1)//r % p:
                while residual % p == 0:
                    residual //= p
        if residual == 1:
            for row in rows:
                yield r*scale, tuple(scale*t for t in row)


def check_maxima():
    degree_lcm = lcm(*(m for m, _ in BASES.values()))
    maxima = [0]*4
    subgroup_maxima = [0]*2
    for n in range(2, degree_lcm+1):
        if degree_lcm % n:
            continue
        rows = list(members(n))
        penta = [(r, taps) for r, taps in rows if len(taps) == 3]
        def oriented(group):
            return sum(1 + (taps != reflection(n, taps)) for _, taps in group)
        values = (len(penta), oriented(penta), len(rows), oriented(rows))
        maxima = list(map(max, maxima, values))
        orders = sorted({r for r, _ in penta})
        for size in range(1, len(orders)+1):
            for selected in combinations(orders, size):
                h = lcm(*selected)
                if h <= 16*n:
                    group = [(r, taps) for r, taps in penta if h % r == 0]
                    subgroup_maxima = list(map(max, subgroup_maxima, (len(group), oriented(group))))
    if degree_lcm != 27720 or maxima != [4, 7, 5, 9] or subgroup_maxima != [3, 6]:
        raise ArithmeticError(f"incorrect maxima: {maxima}, {subgroup_maxima}")
    print("At most four pentanomial reciprocal classes per degree, and at most three in one subgroup.")


def check_prime_indices():
    # In a composite degree with largest proper divisor d one needs 2^d-1 <= 16*d^2.
    failures = {}
    for n in range(2, 101):
        rows = list(members(n))
        for h in range(1, 16*n+1, 2):
            p, rem = divmod((1 << n)-1, h)
            matches = [(r, taps) for r, taps in rows if h % r == 0]
            if rem == 0 and matches and fmpz(p).is_prime():
                failures[n, p] = (sum(len(t) == 1 for _, t in matches),
                                  sum(len(t) == 3 for _, t in matches))
    expected = {(4, 3): (0, 1), (6, 7): (1, 0), (6, 3): (0, 1), (8, 5): (0, 2),
                (8, 3): (0, 2), (9, 7): (1, 3), (10, 31): (0, 2), (10, 11): (0, 2),
                (11, 23): (0, 1), (14, 127): (0, 1)}
    if failures != expected:
        raise ArithmeticError(f"unexpected prime-index failures: {failures}")
    print("Ten degree/prime pairs admit a sparse failure, the last at degree 14 and prime 127.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="decode the low-order classes in one degree")
    parser.add_argument("--ntl", metavar="CENSUS", help="use the NTL cyclotomic factor census")
    args = parser.parse_args()
    if args.degree is not None:
        if args.degree < 2:
            parser.error("the classification starts at degree two")
        for r, taps in sorted(members(args.degree)):
            print(f"order {r}, interior exponents {taps}")
    else:
        cases = candidate_orders()
        supports = verified_bases()
        if args.ntl:
            expected = {key: (sum(len(t) == 1 for t in rows), sum(len(t) == 3 for t in rows))
                        for key, rows in supports.items()}
            if cyclotomic_census(cases, args.ntl) != expected:
                raise ArithmeticError("the NTL counts differ from the verified supports")
        elif flint_census(cases) != supports:
            raise ArithmeticError("the FLINT sparse factors differ from the table")
        print("206 cyclotomic orders give 46 normalized sparse polynomials in 26 reciprocal classes.")
        check_maxima()
        check_prime_indices()
