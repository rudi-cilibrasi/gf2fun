"""Certify the uniform order bound for Ore lifts of primitive binary seeds of degree >= 40.

All counts, degree budgets and comparisons use integers or rational numbers.
Run with python-flint. The final binomials count disjoint choices of numerator
and denominator factors with bounded total degree on each side.
"""

from fractions import Fraction
from functools import cache
from itertools import product
from math import ceil, comb, prod

from flint import fmpz


BASE = 1 << 20
# The numbers of constant-one monic irreducibles of degrees 1, 2, 3 and 4.
PRIME_COUNTS = (1, 1, 2, 3)
TOTAL_DEGREE = sum(k * count for k, count in enumerate(PRIME_COUNTS, 1))
PROFILES = tuple(product(*(range(count + 1) for count in PRIME_COUNTS)))


@cache
def population(degree, profile):
    """Monic constant-one labels with exactly the specified counts of small prime divisors."""
    choices = prod(comb(count, chosen) for count, chosen in zip(PRIME_COUNTS, profile))
    if degree >= TOTAL_DEGREE + 1:
        # Fix the residue modulo Y and each small prime. Each residue has equally many lifts.
        return choices * (1 << (degree - 1 - TOTAL_DEGREE)) * prod(
            ((1 << k) - 1) ** (count - chosen)
            for k, (count, chosen) in enumerate(zip(PRIME_COUNTS, profile), 1))

    total = 0
    for extra in product(*(range(count - chosen + 1) for count, chosen in zip(PRIME_COUNTS, profile))):
        free_degree = degree - sum(k * (chosen + more)
                                   for k, (chosen, more) in enumerate(zip(profile, extra), 1))
        if free_degree < 0:
            continue
        ways = prod(comb(count - chosen, more)
                    for count, chosen, more in zip(PRIME_COUNTS, profile, extra))
        # There is one constant-one quotient of degree zero.
        total += (-1) ** sum(extra) * ways * (1 << max(0, free_degree - 1))
    return choices * total


def families():
    """One block of labels guaranteed to exist at every larger degree scale."""
    for d in range(8, 25):
        shifts = range(max(0, TOTAL_DEGREE + 1 - d) + 1)
        if any(sum(population(d + j, p) for p in PROFILES) != 1 << (d + j - 1) for j in shifts):
            raise ArithmeticError("the divisibility profiles do not partition the labels")
        for profile in PROFILES:
            size = min(population(d + j, profile) // (1 << j) for j in shifts)
            if size < 0:
                raise ArithmeticError("negative profile population")
            if size:
                totient_factor = prod(Fraction((1 << k) - 1, 1 << k) ** chosen
                                      for k, chosen in enumerate(profile, 1))
                yield ceil((1 << d) * totient_factor), size


def allocation(weight, size, rate):
    """Choose the number of distinct labels and maximum total multiplicity on each side."""
    scale = 1 << 60
    value = scale - scale * rate * weight // (1000 * BASE * 4096)
    for _ in range(12):
        value = value * value // scale
    distinct = size * value // (scale + value)
    total = size * value * scale // (scale * scale - value * value)
    if not (0 <= 2 * distinct <= size and distinct <= total):
        raise ArithmeticError("invalid signed multiplicities")
    return distinct, total


def certificate(parity, rows):
    cost = bits = used = 0
    for weight, size in rows:
        chosen, total = allocation(weight, size, (1743, 1233)[parity])
        if chosen == 0:
            continue
        count = (fmpz.bin_uiui(size, chosen) * fmpz.bin_uiui(size - chosen, chosen)
                 * fmpz.bin_uiui(total, chosen) ** 2)
        bits += count.bit_length() - 1
        cost += total * weight
        used += 1
    square_scale = (1 << parity) * BASE ** 2
    if 2 * cost > square_scale - 2 or bits ** 2 <= 25 * square_scale:
        raise ArithmeticError("degree budget or order inequality failed")
    return used, cost, bits


if __name__ == "__main__":
    rows = list(families())
    for parity in (0, 1):
        used, cost, bits = certificate(parity, rows)
        print(f"parity {parity}: {used} families, degree per side <= {cost}, "
              f"at least 2^{bits} distinct fractions per block")
