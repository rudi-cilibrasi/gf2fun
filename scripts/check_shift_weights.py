"""Check equality cases for the two support sizes, primitive translated pairs and the degree-1229 minimizers."""

import csv
from itertools import combinations
from math import gcd, prod

from flint import fmpz

from check_degree_1229 import N, check_known_order
from check_factor_base import DATA, modulus, polynomial
from check_sparse_root_models import X, irreducible_candidate, small_factors
from period_coordinate import mask_of


MINIMIZERS = [(10, 72, 1165), (10, 1101, 1225), (74, 205, 1101),
              (1026, 1036, 1225), (1030, 1101, 1156)]


def check_small_degrees(limit=17):
    shifted_power = [1]
    for _ in range(limit):
        previous = shifted_power[-1]
        shifted_power.append(previous ^ (previous << 1))
    shifts = [0] * (1 << (limit+1))
    equality = [set() for _ in range(limit+1)]
    for f in range(1, len(shifts)):
        bit = f & -f
        shifts[f] = shifts[f ^ bit] ^ shifted_power[bit.bit_length()-1]
        w, t = f.bit_count(), shifts[f].bit_count()
        degree = f.bit_length()-1
        for k in range(degree+1):
            if f >> k & 1 and k.bit_count() > w.bit_length() + t.bit_length() - 2:
                raise ArithmeticError("the binary weight of an exponent exceeds the logarithmic bound")
        if w*t == 1 << degree.bit_count():
            equality[degree].add(f)
    for n, observed in enumerate(equality):
        expected = {shifted_power[j] << (n-j) for j in range(n+1) if j & (n-j) == 0}
        if expected != observed:
            raise ArithmeticError(f"equality classification failed at degree {n}")


def check_primitive_pair(n, i, j, primes):
    order = (1 << n)-1
    if (i+j != n or i & j or gcd(i, j) != 1 or gcd(i*j, order) != 1
            or prod(primes) != order or not all(fmpz(p).is_prime() for p in primes)):
        raise ArithmeticError("invalid transfer parameters or factorization")
    parent = X**n + X**j + 1
    f = 1 + X**i * (1+X)**j
    shifted = 1 + X**j * (1+X)**i
    if f(1+X) != shifted or any(mask_of(p).bit_count() != 5 for p in (f, shifted)):
        raise ArithmeticError("expected a translated pair of pentanomials")
    for polynomial in (parent, f, shifted):
        if X.pow_mod(order, polynomial) != 1 or any(X.pow_mod(order//p, polynomial) == 1 for p in primes):
            raise ArithmeticError(f"a claimed primitive polynomial of degree {n} fails the order test")


def check_four_bit_degrees():
    expected = set()
    for positions in combinations(range(1, 16), 3):
        bits = [1 << k for k in positions]
        n = 1 + sum(bits)
        for bit in bits:
            j = 1 + bit
            if gcd(n, j) == 1:
                expected.add((n, j))
    targets = {(23, 5), (71, 65)}
    if len(expected) != 840 or not targets <= expected:
        raise ArithmeticError("incorrect four-bit degree search space")
    expected -= targets
    with (DATA / "four-bit-translated-pairs.csv").open(newline="") as source:
        rows = csv.reader(source)
        if next(rows) != ["degree", "odd_tap", "proper_factor_hex"]:
            raise ValueError("unexpected obstruction table header")
        for degree, tap, encoded in rows:
            n, j = int(degree), int(tap)
            if (n, j) not in expected:
                raise ValueError("unknown or repeated obstruction")
            expected.remove((n, j))
            f = polynomial(int(encoded, 16))
            if not 0 < f.degree() < n or X.pow_mod(n, f) + X.pow_mod(j, f) + 1 != 0:
                raise ArithmeticError(f"invalid proper factor at {(n, j)}")
    if expected:
        raise ArithmeticError("some four-bit degrees lack certificates")


def main():
    check_small_degrees()
    check_primitive_pair(23, 18, 5, (47, 178481))
    check_primitive_pair(71, 6, 65, (228479, 48544121, 212885833))
    check_four_bit_degrees()
    small = small_factors()
    for taps in MINIMIZERS:
        f = modulus(N, taps)
        if not irreducible_candidate(taps, small) or mask_of(f(1+X)).bit_count() != 33:
            raise ArithmeticError(f"invalid degree-1229 translate at {taps}")
        check_known_order(f)
    print("Checked the support bounds and equality cases through degree 17, all 838 obstructions,"
          " both primitive pairs,"
          " and all five degree-1229 minimizers and their partial orders.")


if __name__ == "__main__":
    main()
