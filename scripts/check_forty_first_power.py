"""Check all sparse degree drops under 41st powering using consecutive subgroup elements."""

import argparse
from functools import cache
from math import gcd

from flint import fmpz, fq_default_ctx

from check_1229_subgroup_traces import minimal_polynomial
from check_cubed_parity import BINARY, X, polynomial
from period_coordinate import mask_of
from check_sparse_circuit_orders import binary_degree, check_ranks
from check_sparse_power_descent import check_independence
from check_sparse_root_orders import cyclotomic_census
from check_trinomial_subfield_pairs import prime_divisors


BASES = ((0, 1, 7, 8, 20), (0, 12, 13, 19, 20))
FINAL = {
    4: {(20, 1271), (60, 8897), (180, 92783)},
    5: {(20, 205), (20, 615), (40, 697), (60, 1435), (40, 2091), (40, 3485),
        (60, 4305), (40, 10455), (60, 12915), (180, 14965), (180, 44895)},
}


@cache
def consecutive_polynomial(order):
    # The nonconstant terms of (X+1)^order are the nonzero binary submasks of order.
    coefficients = [0]*(order+1)
    j = order
    while j:
        coefficients[j] = 1
        j = (j-1) & order
    return (X**order+1).gcd(BINARY(coefficients))


def has_full_relative_degree(order, m, s):
    roots = consecutive_polynomial(order)
    for p in prime_divisors(m//s):
        if roots.degree() == 0:
            break
        in_subfield = roots.gcd(X.pow_mod(1 << (m//p), roots)-X)
        roots = roots // in_subfield
    return roots.degree() > 0


def candidate_orders(d):
    ell, t = 41, 20
    s = t//d
    h = (1 << s)-1
    max_degree = max(t, 2*h*t*t//3)
    candidates = set()
    before_gcd = 0
    for o in range(3, h*max_degree//2+1, 2):
        if o % ell == 0:
            continue
        m = binary_degree(o)
        n, r = d*m, ell*o
        if gcd(m, t) != s or n > max_degree:
            continue
        k = o//gcd(o, h)
        width = min(t, n//k)
        if width < 2 or n**3 > 2*width*r*r or (n > t and 3*(n//t)**2 > 4*h*k):
            continue
        relative = {p: n//binary_degree(r//p) for p in prime_divisors(r)}
        if any(index == p for p, index in relative.items()):
            continue
        # For p=23 use the strengthened square-root bound. For p>25 the ordinary bound suffices.
        if any((p == 23 or p > 25) and index % ((p-1)//2) == 0 for p, index in relative.items()):
            continue
        before_gcd += 1
        if n == t or has_full_relative_degree(h*k, m, s):
            candidates.add((n, r))
    if before_gcd != {4: 17, 5: 155}[d] or candidates != FINAL[d]:
        raise ArithmeticError(f"unexpected order sieve for index {d}: {before_gcd}, {candidates}")
    count = sum(int(fmpz(r).euler_phi())//n for n, r in candidates)
    if count != {4: 660, 5: 600}[d]:
        raise ArithmeticError("incorrect number of cyclotomic factors")
    print(f"Index {d}: {before_gcd} orders before the consecutive-element test, "
          f"{len(candidates)} after it, and {count} binary factors.")
    return sorted(candidates)


@cache
def field_modulus(n):
    modulus = fq_default_ctx(2, n).modulus()
    if modulus.degree() != n or not modulus.is_irreducible():
        raise ArithmeticError(f"incorrect binary field model in degree {n}")
    return modulus


def flint_census(orders):
    # An independent construction: generate the order-r subgroup in a field of
    # degree n, then recover the first binary linear dependence for each orbit.
    found = {}
    for n, r in orders:
        modulus = field_modulus(n)
        field = mask_of(modulus)
        factors = prime_divisors(r)
        for mask in range(2, 1 << n):
            candidate = BINARY([(mask >> i) & 1 for i in range(mask.bit_length())])
            root = candidate.pow_mod(((1 << n)-1)//r, modulus)
            if all(root.pow_mod(r//p, modulus) != 1 for p in factors):
                break
        else:
            raise ArithmeticError(f"no generator of the order-{r} subgroup")
        if root.pow_mod(r, modulus) != 1:
            raise ArithmeticError("incorrect subgroup projection")
        seen = set()
        polynomials = set()
        for e in range(1, r):
            if e in seen or gcd(e, r) != 1:
                continue
            conjugate = e
            while conjugate not in seen:
                seen.add(conjugate)
                conjugate = 2*conjugate % r
            poly = minimal_polynomial(mask_of(root.pow_mod(e, modulus)), field)
            if poly.bit_length() != n+1 or poly in polynomials:
                raise ArithmeticError(f"invalid or repeated minimal polynomial at order {r}")
            polynomials.add(poly)
        if len(seen) != fmpz(r).euler_phi() or len(polynomials)*n != len(seen):
            raise ArithmeticError(f"incomplete Frobenius orbits at order {r}")
        weights = [poly.bit_count() for poly in polynomials]
        if min(weights) <= 5:
            found[n, r] = (weights.count(3), weights.count(5))
    return found


def verify_bases():
    for g in (1, 31):
        for support in BASES:
            f = polynomial(i*g for i in support)
            r = 1271*g
            if not f.is_irreducible() or X.pow_mod(r, f) != 1 or any(
                X.pow_mod(r//p, f) == 1 for p in (31, 41)
            ):
                raise ArithmeticError(f"incorrect root order in degree {20*g}")
    print("Both order-1271 bases and their first dilations have the claimed degrees and orders.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ntl', metavar='CENSUS', help='use the faster NTL cyclotomic factor verifier')
    args = parser.parse_args()
    check_ranks(41, 4, {(3, 3): 780, (4, 3): 40, (4, 4): 9840, (5, 4): 5670, (5, 5): 85720})
    check_ranks(41, 5, {(3, 3): 780, (4, 3): 240, (4, 4): 9640, (5, 4): 91390})
    check_independence(41, 2, 5)
    orders = candidate_orders(4) + candidate_orders(5)
    census = cyclotomic_census(orders, args.ntl) if args.ntl else flint_census(orders)
    if census != {(20, 1271): (0, 2)}:
        raise ArithmeticError(f"unexpected sparse factors: {census}")
    verify_bases()
