"""Check twisted cyclotomic pentanomials and the remaining quadratic-lift supports."""

import json
from collections import Counter
from math import isqrt, prod
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


if __name__ == "__main__":
    check_orders()
