"""Check twisted cyclotomic pentanomials and the remaining quadratic-lift supports."""

import argparse
import json
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt, lcm, prod
from pathlib import Path

from flint import fmpz, nmod_poly

from check_product_range import prime_index_powers


X = nmod_poly([0, 1], 2)
DATA = Path(__file__).resolve().parents[1] / "data" / "translation-lift-orders.json"


def cyclotomic_form(m):
    """Expand (X+w)^m + (X+w²)^m by Lucas' rule, w²+w+1=0."""
    coefficients = [0] * m
    j = m
    while j:
        if j % 3:
            coefficients[m - j] = 1
        j = (j - 1) & m
    return nmod_poly(coefficients, 2)


def orbit_degrees(m):
    remaining = set(range(1, m))
    counts = Counter()
    while remaining:
        i = next(iter(remaining))
        degree = 0
        while i in remaining:
            remaining.remove(i)
            degree += 1
            i = -2 * i % m
        counts[degree] += 1
    return counts


def lift(k, j, triangle):
    q = 2**k
    if triangle:
        return 1 + X**5 + X**(2**j) + X**(q + 1) + X**(q + 4)
    return 1 + (X**q + X**(2**j)) * (X**4 + X)


def check_finite_cases():
    for m in range(3, 152, 2):
        factors = cyclotomic_form(m).factor()[1]
        if any(e != 1 for _, e in factors):
            raise ValueError(f"repeated factor for m={m}")
        if Counter(f.degree() for f, _ in factors) != orbit_degrees(m):
            raise ValueError(f"incorrect Frobenius orbits for m={m}")

    expected = {(3, 1, True), (3, 3, True), (4, 1, False),
                (5, 1, True), (5, 5, True), (11, 11, True)}
    irreducibles = set()
    for k in range(3, 12):
        for triangle in (True, False):
            taps = range(1, k + 1, 2) if triangle else (j for j in range(1, k) if j != 2)
            for j in taps:
                f = lift(k, j, triangle)
                if f.factor()[1] == [(f, 1)]:
                    irreducibles.add((k, j, triangle))
        if k % 2 and lift(k, k, True) != cyclotomic_form(2**k + 5):
            raise ValueError(f"incorrect cyclotomic support for k={k}")
    if irreducibles != expected:
        raise ValueError(f"unexpected irreducible supports {irreducibles ^ expected}")
    return irreducibles


def check_factors(factors, value):
    if prod(factors) != value or not all(fmpz(p).is_prime() for p in set(factors)):
        raise ValueError(f"incomplete prime factorization for {value.bit_length()}-bit integer")


def odd_survival_density(classes):
    """Inclusion-exclusion on odd integers, merging congruences by CRT."""
    def remaining(i, a, m):
        if i == len(classes):
            return Fraction(1, m)
        d, b = classes[i]
        common = gcd(m, d)
        result = remaining(i + 1, a, m)
        if (b - a) % common:
            return result
        step = ((b - a) // common * pow(m // common, -1, d // common)) % (d // common)
        return result - remaining(i + 1, a + m * step, lcm(m, d))

    return 2 * remaining(0, 1, 2)


def check_remaining_exponents(data):
    """Use proper divisors for A_k and integer order obstructions for C_k."""
    odd = set(range(7, 192, 2))
    surviving = odd.copy()
    factors = [int(mask, 16) for mask in data["residual_factors"]]
    classes = []
    if len(set(factors)) != len(factors):
        raise ValueError("duplicate residual factor")
    for mask in factors:
        f = nmod_poly([(mask >> i) & 1 for i in range(mask.bit_length())], 2)
        if f.degree() < 1 or f.factor()[1] != [(f, 1)]:
            raise ValueError(f"invalid residual factor {mask:#x}")
        value = X
        b = (X**4 + X) % f
        residues = set()
        for k in range(1, 192):
            value = (value * value) % f
            if ((value + X) * b + 1) % f == 0:
                residues.add(k % f.degree())
                if f.degree() < 2**k + 4:
                    surviving.discard(k)
        if len(residues) != 1:
            raise ValueError(f"missing or inconsistent periodic factor {mask:#x}")
        classes.append((f.degree(), residues.pop()))
    if surviving != {71, 101, 155}:
        raise ValueError(f"unexpected residual exponents {sorted(surviving)}")
    density = odd_survival_density(sorted(classes))
    if density != Fraction(168082781184, 1726082838425):
        raise ValueError(f"unexpected odd-exponent density {density}")

    known = {int(k) for k in data["torus_prime_minus_one"]}
    for k in range(3, 192, 2):
        if k in known:
            continue
        n = 2**k + 4
        if pow(-2, n, n + 1) != 1:
            continue
        if not any(n % l == 0 and pow(-2, n // l, n + 1) == 1 for l in (3, 11)):
            raise ValueError(f"missing modular-order obstruction for k={k}")
    print("Above degree 20 through 2^191+4, the only remaining projectively symmetric")
    print("primitive candidates, up to reciprocity, are A_71, A_101, A_155, C_141, C_191.")
    print(f"The twenty divisors leave density {density} among all odd exponents for A_k.")


def check_orders():
    data = json.loads(DATA.read_text())
    for exponent, factors in data["torus_prime_minus_one"].items():
        k = int(exponent)
        n = 2**k + 4
        p = n + 1
        check_factors(factors, n)
        if pow(-2, n, p) != 1 or any(pow(-2, n // l, p) == 1 for l in set(factors)):
            raise ValueError(f"incorrect modular order for k={k}")
        # Order p-1 forces p prime. Check it independently as well.
        if not fmpz(p).is_prime() or isqrt((n - 1) // 2) != 2**((k - 1) // 2):
            raise ValueError(f"incorrect degree or root-order bound for k={k}")
        print(f"k={k}: prime 2^k+5, modular order 2^k+4, binary root order >= 2^(2^{(k+1)//2}).")

    indices = {(3, 1, True): 3, (3, 3, True): 1, (4, 1, False): 1,
               (5, 1, True): 9, (5, 5, True): 3, (11, 11, True): 7}
    if check_finite_cases() != indices.keys():
        raise ValueError("incomplete finite order table")
    for (k, j, triangle), index in indices.items():
        f = lift(k, j, triangle)
        n = f.degree()
        group = 2**n - 1
        factors = data["binary_group_order"][str(n)]
        check_factors(factors, group)
        order = group // index
        if order * index != group or X.pow_mod(order, f) != 1:
            raise ValueError(f"incorrect full power for {(k, j, triangle)}")
        primes = sorted(l for l in set(factors) if order % l == 0)
        if any(value == 1 for _, value in prime_index_powers(X, order, primes, f)):
            raise ValueError(f"incorrect exact order for {(k, j, triangle)}")
        print(f"degree {n}, {'triangle' if triangle else 'cycle'} j={j}: exact index {index}.")
    check_remaining_exponents(data)


def check_extended_cyclotomic():
    """Exclude all odd k strictly between 191 and 16541 by integer arithmetic."""
    small_primes = fmpz.primorial_ui(8192)
    two = fmpz(2)
    small_factor_count = 0
    fermat_failures = 0
    cubic_obstructions = []
    for k in range(193, 16541, 2):
        p = two**k + 5
        n = p - 1
        if p.gcd(small_primes) > 1:
            small_factor_count += 1
            continue
        if pow(two, n, p) != 1:
            fermat_failures += 1
            continue
        if pow(two, n // 3, p) != 1:
            raise ValueError(f"no exclusion at k={k}")
        cubic_obstructions.append(k)
    if (small_factor_count, fermat_failures, cubic_obstructions) != (7126, 1046, [273, 341]):
        raise ValueError("unexpected counts for the cyclotomic exponents")
    print("Every C_k for odd 191 < k < 16541 is reducible.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extended-cyclotomic", action="store_true",
                        help="also check all odd exponents below 16541")
    args = parser.parse_args()
    check_orders()
    if args.extended_cyclotomic:
        check_extended_cyclotomic()
