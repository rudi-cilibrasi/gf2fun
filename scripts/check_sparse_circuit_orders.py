"""Classify the index-four thirteenth-power exceptions and check the circuit ranks for 41."""

import argparse
from collections import Counter
from math import gcd

from flint import fmpz

from check_cubed_parity import X, polynomial
from check_sparse_power_descent import columns, insert
from check_sparse_root_orders import cyclotomic_census
from check_trinomial_subfield_pairs import prime_divisors


BASES = ((0, 1, 9, 10, 12), (0, 2, 3, 11, 12))
EXPECTED = ((12, 91), (132, 2093), (276, 4277), (420, 6461), (996, 15197),
            (1140, 17381), (1428, 21749), (1572, 23933), (1860, 28301),
            (2148, 32669), (2292, 34853), (3036, 98371))


def binary_degree(order):
    degree = int(fmpz(order).euler_phi())
    for p in prime_divisors(degree):
        while degree % p == 0 and pow(2, degree//p, order) == 1:
            degree //= p
    return degree


def check_ranks(ell, s, expected):
    dimension, blocks = columns(ell, s)
    counts = Counter()

    def visit(start, size, basis, rank):
        if size >= 3:
            counts[size, rank] += 1
        if size == 5:
            return
        for j in range(start, ell):
            enlarged = basis.copy()
            gain = sum(insert(enlarged, v) for v in blocks[j])
            increment, remainder = divmod(gain, s)
            if remainder:
                raise ArithmeticError("binary rank increment is not a subfield dimension")
            visit(j+1, size+1, enlarged, rank+increment)

    initial = [0]*dimension
    if not all(insert(initial, v) for v in blocks[0]):
        raise ArithmeticError("invalid coefficient basis")
    visit(1, 1, initial, 1)
    if counts != expected:
        raise ArithmeticError(f"unexpected column ranks at {ell} over base degree {s}: {counts}")
    print(f"ell={ell}, s={s}: all triples independent, every five columns span at least four.")


def thirteenth_cases():
    ell, t, s = 13, 12, 3
    multiplier = (1 << s)-1
    max_degree = (ell*multiplier)**2
    cases = []
    for order in range(3, multiplier*max_degree//2 + 1, 2):
        if order % ell == 0:
            continue
        m = binary_degree(order)
        n, full = 4*m, ell*order
        if gcd(t, m) != s or n > max_degree:
            continue
        step = order//gcd(order, multiplier)
        if not any(n**3 <= 2*j*full**2 for j in range(2, min(t, n//step)+1)):
            continue
        if any(n % p == 0 and binary_degree(full//p) == n//p for p in prime_divisors(full)):
            continue
        cases.append((n, full))
    if tuple(sorted(cases)) != EXPECTED:
        raise ArithmeticError(f"unexpected normalized orders: {cases}")
    factors = 0
    for n, order in cases:
        if binary_degree(order) != n:
            raise ArithmeticError("incorrect binary degree of candidate order")
        factors += int(fmpz(order).euler_phi())//n
        if order == 91:
            continue
        # A quadratic-residue defining set in this prime component excludes weight five.
        if not any(p > 21 and p % 4 == 3 and (n//binary_degree(order//p)) % ((p-1)//2) == 0
                   for p in prime_divisors(order)):
            raise ArithmeticError(f"no quadratic-residue exclusion at order {order}")
    if factors != 150:
        raise ArithmeticError("incorrect candidate factor count")
    print("Exactly 12 normalized orders with 150 binary factors survive packing. "
          "A quadratic-residue component excludes every order except 91.")
    return cases


def check_bases():
    factors = (X**91+1).factor()[1]
    sparse = set()
    for f, e in factors:
        if e != 1 or not f.is_irreducible():
            raise ArithmeticError("invalid order-91 factorization")
        if X.pow_mod(7, f) == 1 or X.pow_mod(13, f) == 1:
            continue
        support = tuple(i for i, c in enumerate(f.coeffs()) if c)
        if len(support) <= 5:
            sparse.add(support)
    if sparse != set(BASES):
        raise ArithmeticError(f"unexpected normalized bases: {sparse}")
    for k in range(4):
        g = 7**k
        for base in BASES:
            f = polynomial(e*g for e in base)
            if not f.is_irreducible() or X.pow_mod(91*g, f) != 1 or any(
                X.pow_mod(91*g//p, f) == 1 for p in (7, 13)
            ):
                raise ArithmeticError(f"incorrect dilation in degree {12*g}")
    print("Both bases have order 91. Both dilations were checked through degree 4116.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ntl', metavar='CENSUS', help='also split all 150 candidate factors independently')
    args = parser.parse_args()
    check_ranks(13, 3, {(3, 3): 66, (4, 3): 16, (4, 4): 204, (5, 4): 495})
    check_ranks(41, 4, {(3, 3): 780, (4, 3): 40, (4, 4): 9840, (5, 4): 5670, (5, 5): 85720})
    check_ranks(41, 5, {(3, 3): 780, (4, 3): 240, (4, 4): 9640, (5, 4): 91390})
    orders = thirteenth_cases()
    check_bases()
    if args.ntl:
        if cyclotomic_census(orders, args.ntl) != {(12, 91): (0, 2)}:
            raise ArithmeticError("the complete NTL factor census differs")
        print("The independent NTL census found exactly the two expected pentanomials.")
