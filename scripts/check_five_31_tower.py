"""Verify the two-bit count for the mixed-prime exceptions in degrees 5*31^j."""

from collections import Counter
from itertools import combinations, permutations
from math import comb

from check_cyclotomic_row_isolation import check_modulo_31
from check_factor_base import irreducible, modulus, polynomial
from make_witnesses import gcd as polynomial_gcd, x_power


def has_unique_sum(taps, rows, modulus):
    # The unassigned rows carry the common residue zero. Every choice of
    # three different rows gives one distinct assignment to the singleton taps.
    sums = Counter((a*taps[0] + b*taps[1] + c*taps[2]) % modulus for a, b, c in rows)
    return 1 in sums.values()


def check_lifts():
    templates = check_modulo_31()
    modulus = 31**2
    h = pow(2, 31, modulus)
    if h != 374 or pow(h, 5, modulus) != 1 or h % 31 != 2:
        raise ArithmeticError("incorrect lifted Frobenius weight")
    rows = list(permutations([pow(h, i, modulus) for i in range(5)], 3))
    tested = 0
    for _, b, c in sorted(templates):
        for v in range(b, modulus, 31):
            for w in range(c, modulus, 31):
                if not has_unique_sum((1, v, w), rows, modulus):
                    raise ArithmeticError(f"unresolved lifted residues {v}, {w}")
                tested += 1
    if tested != 7688:
        raise ArithmeticError(f"incorrect lift count {tested}")

    weights = [pow(2, i, 31) for i in range(5)]
    four_rows = [list(permutations(subset, 3)) for subset in combinations(weights, 4)]
    triples = list(combinations(range(1, 31), 3))
    if len(triples) != 4060 or not all(
        any(has_unique_sum(taps, row, 31) for row in four_rows) for taps in triples
    ):
        raise ArithmeticError("a four-column determinant has no isolated assignment")
    print(f"Verified {tested} lifts modulo 961 and {len(triples)} four-column tests modulo 31.")


def check_orders():
    x = polynomial(2)
    bases = []
    for interior in (1, 3):
        for taps in combinations(range(1, 5), interior):
            f = modulus(5, taps)
            if irreducible(f):
                if x.pow_mod(31, f) != 1 or x.pow_mod(1, f) == 1:
                    raise ArithmeticError(f"incorrect base order for {taps}")
                bases.append(taps)
    if [t for t in bases if len(t) == 1] != [(2,), (3,)] or len(bases) != 6:
        raise ArithmeticError(f"incorrect sparse irreducibles of degree five {bases}")
    indices = []
    for j in (1, 2, 3):
        multiplier = 31**j
        n, order = 5*multiplier, 31*multiplier
        if pow(2, n, order) != 1 or any(pow(2, n//d, order) == 1 for d in (5, 31)):
            raise ArithmeticError(f"incorrect binary degree at level {j}")
        for taps in bases:
            f = sum(1 << (multiplier*k) for k in (0, *taps, 5))
            if x_power(order, f) != 1 or polynomial_gcd(f, x_power(order//31, f)^1) != 1:
                raise ArithmeticError(f"incorrect expanded root order for {taps} at level {j}")
        indices.append((comb(n-1, 3)-1).bit_length())
    if indices != [20, 35, 49]:
        raise ArithmeticError(f"incorrect unrestricted support code widths {indices}")
    print("All eighteen quotient rings in degrees 155, 4805 and 148955 passed the "
          "root-order and binary-degree checks.")


if __name__ == "__main__":
    check_lifts()
    check_orders()
