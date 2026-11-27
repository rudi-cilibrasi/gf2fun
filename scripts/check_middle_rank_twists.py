"""Check middle-rank failures and cubic-root twists of odd-degree binary irreducibles."""

import csv
import gzip
from collections import Counter
from itertools import combinations
from math import lcm

from flint import fmpz

from check_factor_base import DATA, irreducible, polynomial


def dyadic_order(h):
    power, degree = 2 % h, 1
    while power != 1:
        power = 2*power % h
        degree += 1
    return degree


def check_indices():
    middle = 0
    for index in range(3, 4096, 2):
        period = dyadic_order(index)
        n = lcm(2, period)
        order = ((1 << n)-1)//index
        only_middle = all((j*order).bit_count() == n//2 for j in range(1, index))
        minus_one = period % 2 == 0 and pow(2, period//2, index) == index-1
        valuations = set()
        for p, _ in fmpz(index).factor():
            d = dyadic_order(int(p))
            valuations.add((d & -d).bit_length()-1)
        if only_middle != minus_one or only_middle != (len(valuations) == 1 and 0 not in valuations):
            raise ArithmeticError(f"middle-rank criterion failed at index {index}")
        middle += only_middle
    return middle


def twist_support(support):
    terms = {2*i for i in support}
    for i, j in combinations(support, 2):
        if (i-j) % 3:
            terms.symmetric_difference_update((i+j,))
    return tuple(sorted(terms))


def root_order(f):
    order = (1 << f.degree())-1
    x = polynomial(2)
    for p, e in fmpz(order).factor():
        p = int(p)
        for _ in range(e):
            if x.pow_mod(order//p, f) != 1:
                break
            order //= p
    return order


def first_weight(order, n):
    # Positive multiples include the word of all ones.
    counts = Counter(word.bit_count() for word in range(order, 1 << n, order))
    first = min(counts)
    return first, counts[first]


def from_exponents(terms):
    return polynomial(sum(1 << i for i in terms))


def check_small_twists():
    count = primitive = 0
    for m in range(3, 12, 2):
        for mask in range((1 << m)+1, 1 << (m+1), 2):
            g = polynomial(mask)
            if not irreducible(g):
                continue
            count += 1
            terms = twist_support(tuple(i for i in range(m+1) if mask >> i & 1))
            f = from_exponents(terms)
            if not irreducible(f) or (mask.bit_count() == 3 and len(terms) != 5):
                raise ArithmeticError(f"incorrect norm polynomial at seed {g}")
            base_order, lifted_order = root_order(g), root_order(f)
            k, multiplicity = first_weight(base_order, m)
            predicted = multiplicity*((1 << k)+2*(-1)**k)//3
            if lifted_order != 3*base_order or first_weight(lifted_order, 2*m) != (k, predicted):
                raise ArithmeticError(f"incorrect order or first failing rank at seed {g}")
            if k == m:
                primitive += 1
                if base_order != (1 << m)-1 or predicted != ((1 << m)-2)//3:
                    raise ArithmeticError("incorrect middle-rank multiplicity")
    return count, primitive


def check_large_twists():
    x = polynomial(2)
    for a in (3, 511):
        m = 2047
        f = from_exponents(twist_support((0, a, m)))
        if not irreducible(f):
            raise ArithmeticError(f"degree-4094 twist is reducible for tap {a}")
        z = x.pow_mod((1 << m)-1, f)
        beta = x*z.pow_mod(2, f) % f
        if z*z % f + z + 1 != 0 or beta.pow_mod(m, f) + beta.pow_mod(a, f) + 1 != 0:
            raise ArithmeticError(f"failed to recover the degree-2047 seed at tap {a}")
    # The input is the published primitive trinomial of Brent and Zimmermann.
    if twist_support((0, 9156813, 74207281)) != (0, 18313626, 74207281, 83364094, 148414562):
        raise ArithmeticError("incorrect support for the degree-148414562 twist")


def check_degree_1229():
    counts = Counter()
    with gzip.open(DATA/"degree-1229-irreducible-supports.csv.gz", "rt", newline="") as stream:
        for row in csv.DictReader(stream):
            terms = (0, int(row["a"]), int(row["b"]), int(row["c"]), 1229)
            counts[len(twist_support(terms))] += 2  # The other reciprocal has the same weight.
    if counts != {9: 65234, 11: 176426, 13: 397506}:
        raise ArithmeticError(f"incorrect degree-1229 twist census {counts}")
    return counts


if __name__ == "__main__":
    print(f"Checked every odd index from 3 to 4095. Only the middle rank fails at {check_indices()} indices.")
    count, primitive = check_small_twists()
    print(f"Checked exact orders, first ranks and multiplicities for all {count} seeds in odd degrees 3 through 11.")
    print(f"The {primitive} primitive seeds first fail at the middle rank after twisting.")
    check_large_twists()
    print("Verified both degree-4094 fields and the support of the degree-148414562 example.")
    for weight, count in sorted(check_degree_1229().items()):
        print(f"{count:,} degree-1229 irreducibles give degree-2458 twists with {weight} terms.")
