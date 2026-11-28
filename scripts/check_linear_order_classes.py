"""Classify sparse binary polynomials through the sharp two-bit root-order threshold."""

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

# The normalized bases with 16 < r/n <= 127/7.
BOUNDARY_BASES = {
    127: (7, [(1,), (3,), (1, 2, 3), (1, 2, 5), (1, 3, 5), (1, 3, 6), (2, 3, 4)]),
    195: (12, [(2, 4, 5)]), 257: (16, [(1, 8, 15), (3, 8, 13)]),
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


def candidate_orders(boundary=False):
    # For a normalized support, den*r <= num*n and 5*n^4 <= 16*r^3 bound r.
    num, den = (127, 7) if boundary else (16, 1)
    bound = 16*num**4 // (5*den**4)
    degrees = [0]*(bound+1)
    degrees[1] = 1
    cases = []
    normalized = 0
    for r in range(3, bound+1, 2):
        n = degrees[r] = binary_degree(r)
        if den*r > num*n or (boundary and r <= 16*n) or 5*n**4 > 16*r**3:
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
    if (normalized, len(cases)) != ((2895, 55) if boundary else (4760, 206)):
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


def verified_bases(bases):
    found = {}
    for r, (n, representatives) in bases.items():
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


def check_unit_records(limit=255):
    """Compare unit traces of every primitive-root orbit for small odd orders."""
    checked = 0
    for r in range(3, limit+1, 2):
        n = binary_degree(r)
        units = [j for j in range(1, r) if gcd(j, r) == 1]
        phi = BINARY([int(c) % 2 for c in fmpz_poly.cyclotomic(r)])
        _, factors = phi.factor()
        records = set()
        normalized = not any(n == p*binary_degree(r//p) for p in prime_divisors(r) if r % (p*p) == 0)
        for f, multiplicity in factors:
            exponents = [j for j, c in enumerate(f) if j and c]
            if f.degree() != n or multiplicity != 1 or (gcd(*exponents) == 1) != normalized:
                raise ArithmeticError(f"unexpected exponent gcd at order {r}")
            # The coefficients at positive j are the traces of inverse-root powers.
            trace = (X*f.derivative()*f.inverse_series_trunc(r)).truncate(r)
            word = tuple(int(trace[j]) for j in units)
            if normalized != any(word) or (normalized and word in records):
                raise ArithmeticError(f"unit traces failed to separate the factors at {r}")
            records.add(word)
            checked += 1
            if not normalized or n % 2 == 0:
                continue
            # Enlarge the order, including both new primes and repeated prime factors.
            ambient = 15*r
            for p in prime_divisors(ambient):
                d = ambient//p
                entries = {}
                for j in range(1, ambient):
                    if gcd(j, ambient) == 1:
                        bit = int(trace[j % r])
                        if entries.setdefault(j % d, bit) != bit:
                            break
                else:
                    if d % r:
                        raise ArithmeticError(f"odd-degree record descended below order {r}")
                    continue
                if d % r == 0:
                    raise ArithmeticError(f"unit record did not descend to a multiple of {r}")
    print(f"Checked unit traces on all {checked} Frobenius orbits of odd orders through {limit}.")


def members(n, bases=BASES):
    """Yield (root order, canonical taps) in a given degree without factoring that degree."""
    for r, (m, rows) in bases.items():
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


def check_maxima(boundary):
    # For the sharp open interval, omit precisely the normalized order-127 row.
    bases = BASES
    if boundary:
        bases = BASES | {r: v for r, v in BOUNDARY_BASES.items() if r != 127}
    degree_lcm = lcm(*(m for m, _ in bases.values()))
    maxima = [0]*4
    subgroup_maxima = [0]*2
    for n in range(2, degree_lcm+1):
        if degree_lcm % n:
            continue
        rows = list(members(n, bases))
        penta = [(r, taps) for r, taps in rows if len(taps) == 3]
        def oriented(group):
            return sum(1 + (taps != reflection(n, taps)) for _, taps in group)
        values = (len(penta), oriented(penta), len(rows), oriented(rows))
        maxima = list(map(max, maxima, values))
        orders = sorted({r for r, _ in penta})
        for size in range(1, len(orders)+1):
            for selected in combinations(orders, size):
                h = lcm(*selected)
                fits = 7*h < 127*n if boundary else h <= 16*n
                if fits:
                    group = [(r, taps) for r, taps in penta if h % r == 0]
                    subgroup_maxima = list(map(max, subgroup_maxima, (len(group), oriented(group))))
    if (degree_lcm != (55440 if boundary else 27720) or maxima != [4, 7, 5, 9]
            or subgroup_maxima != [3, 6]):
        raise ArithmeticError(f"incorrect maxima: {maxima}, {subgroup_maxima}")
    print("At most four pentanomial reciprocal classes per degree, and at most three in one subgroup.")
    if boundary:
        for n in (7, 7*127):
            endpoint = [(r, t) for r, t in members(n, BOUNDARY_BASES) if len(t) == 3 and 7*r == 127*n]
            if len(endpoint) != 5 or any(r != 127*(n//7) for r, _ in endpoint):
                raise ArithmeticError("expected five pentanomial classes in a single endpoint subgroup")
        print("Five reciprocal classes have order exactly 127n/7 at n = 7 times every power of 127.")


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
    parser.add_argument("--sharp", action="store_true", help="include the classifications through 127n/7")
    args = parser.parse_args()
    if args.degree is not None:
        if args.degree < 2:
            parser.error("the classification starts at degree two")
        for r, taps in sorted(members(args.degree, BASES | BOUNDARY_BASES if args.sharp else BASES)):
            print(f"order {r}, interior exponents {taps}")
    else:
        cases = candidate_orders()
        bases = BASES
        if args.sharp:
            cases += candidate_orders(boundary=True)
            bases = BASES | BOUNDARY_BASES
        supports = verified_bases(bases)
        if args.ntl:
            expected = {key: (sum(len(t) == 1 for t in rows), sum(len(t) == 3 for t in rows))
                        for key, rows in supports.items()}
            if cyclotomic_census(cases, args.ntl) != expected:
                raise ArithmeticError("the NTL counts differ from the verified supports")
        elif flint_census(cases) != supports:
            raise ArithmeticError("the FLINT sparse factors differ from the table")
        print(f"{len(cases)} cyclotomic orders give {sum(map(len, supports.values()))} normalized "
              f"sparse polynomials in {sum(len(rows) for _, rows in bases.values())} reciprocal classes.")
        check_unit_records()
        check_maxima(args.sharp)
        check_prime_indices()
