"""Certify trinomial root-product tests for n = e + 2^s + 2^t. Requires python-flint."""

from functools import cache
from itertools import combinations_with_replacement
from math import gcd, lcm

from flint import nmod_mpoly_ctx, nmod_poly
from sympy import factorint, n_order

from check_trinomial_triples import pair_and_triple_counts


X = nmod_poly([0, 1], 2)
SYMMETRIC = nmod_mpoly_ctx.get(("S", "P"), 2)
S, P = SYMMETRIC.gens()
TAPS = {1: (3, 4, 5, 7), 2: (3, 7, 11)}


# Each row covers n=e+2^s+2^t with s,t positive, while requiring gcd(n,a)=1.
NORMALIZED_TAPS = {
    1: (3, 5, 7, 9),       2: (3, 5, 7, 21),       3: (1, 2, 6, 7),
    4: (5, 7, 9, 17, 21),  5: (2, 3, 4, 7),        6: (3, 5, 7, 15, 19),
    7: (1, 2, 4, 5, 9),    8: (1, 3, 5, 9, 13),    9: (2, 3, 4, 7, 15),
    10: (1, 3, 7, 9, 21), 11: (2, 3, 13, 15, 17), 12: (3, 5, 7, 9, 17),
    13: (2, 3, 4, 7),     14: (3, 7, 9, 13),      15: (1, 2, 3, 4, 5, 17),
    16: (3, 5, 7, 9),     17: (1, 2, 3, 4, 6),    18: (1, 3, 5, 9, 17),
    19: (1, 2, 3, 4, 17), 20: (1, 5, 7, 9),       21: (1, 3, 5, 7, 9),
    22: (1, 3, 5, 7),     23: (3, 5, 7, 9, 17),   24: (1, 5, 7, 9),
    25: (1, 3, 7, 9, 17), 26: (1, 3, 7, 9, 21),   27: (2, 3, 4, 13),
    28: (3, 7, 9),        29: (2, 3, 7, 9),       30: (3, 5, 7, 9),
    31: (1, 2, 3, 4),     32: (1, 3, 7, 9),
}


@cache
def power_sum(k):
    """b^k+c^k in S=b+c and P=bc, in characteristic two."""
    if k == 0:
        return SYMMETRIC.constant(0)
    if k == 1:
        return S
    return S * power_sum(k - 1) + P * power_sum(k - 2)


def cross(f, g):
    """f(b)g(c)+f(c)g(b), expressed in S and P."""
    return sum((P**min(i, j) * power_sum(abs(i-j))
                for i, a in enumerate(f.coeffs()) if a
                for j, b in enumerate(g.coeffs()) if b), SYMMETRIC.constant(0))


def commutation_polynomial(e, a):
    """Clear denominators in the resultant for the common Frobenius iterate."""
    if e < 1 or a < 1:
        raise ValueError("the offset and the inner exponent must be positive")
    m = max(e, a)
    denominator = X**m * (X+1)**max(e-a, 0)
    product_num = X**(m-e) * (X+1)**(a+max(e-a, 0))
    translated_num = X**(m-a) * (X+1)**max(a-e, 0)
    sum_num = denominator + product_num + translated_num
    # For H(b,Y), H(c,Y) the quadratic resultant is the sum of these two terms.
    resultant = (cross(denominator, product_num)**2
                 + cross(denominator, sum_num) * cross(sum_num, product_num))
    if resultant.is_zero():
        raise ValueError(f"the correspondence for e={e}, a={a} gives no restriction")
    degree = max(i+j for i, j in resultant.monoms())
    polynomial = sum((sum_num**i * product_num**j * denominator**(degree-i-j)
                      for (i, j), _ in resultant.terms()), 0*X)
    if polynomial.is_zero():
        raise ValueError(f"the specialized resultant for e={e}, a={a} is zero")
    return polynomial


def frobenius_orbit(x, modulus):
    values = [x % modulus]
    for _ in range(1, modulus.degree()):
        values.append(values[-1]**2 % modulus)
    return values


def inverse(x, modulus):
    divisor, coefficient, _ = x.xgcd(modulus)
    if not divisor.is_one():
        raise ArithmeticError("a denominator vanished in the quotient field")
    return coefficient % modulus


@cache
def possible_classes(e, a):
    """Necessary residue pairs for a product-one triple, grouped by factor degree."""
    classes = {}
    for modulus, _ in commutation_polynomial(e, a).factor()[1]:
        degree = modulus.degree()
        if degree == 1:  # u and u+1 are both nonzero at every admissible point.
            continue
        orbit = frobenius_orbit(X, modulus)
        positions = {tuple(value.coeffs()): i for i, value in enumerate(orbit)}
        reciprocal = inverse(X, modulus)
        inverses = frobenius_orbit(reciprocal, modulus)
        product = (1+X).pow_mod(a, modulus) * reciprocal.pow_mod(e, modulus) % modulus
        phi = inverse(1+X, modulus)
        translated = frobenius_orbit(phi, modulus)
        base, target = phi.pow_mod(e, modulus), (1+phi).pow_mod(a, modulus)
        hits = set()
        for i, reciprocal_i in enumerate(inverses):
            # The first equation fixes the partner of the i-th conjugate.
            partner = product * reciprocal_i % modulus
            j = positions.get(tuple(partner.coeffs()))
            if j is not None and i <= j and base * translated[i] * translated[j] % modulus == target:
                hits.add((i, j))
        if hits:
            classes.setdefault(degree, set()).update(hits)
    return classes


def forbidden_classes(e, a, normalized):
    classes = {d: hits.copy() for d, hits in possible_classes(e, a).items()}
    if normalized:
        for p in factorint(a):
            if p == 2:
                if e % 2 == 0:  # s,t are positive, so n has the parity of e.
                    classes.setdefault(1, set()).add((0, 0))
                continue
            d = int(n_order(2, p))
            powers = [pow(2, j, p) for j in range(d)]
            hits = {(i, j) for i, j in combinations_with_replacement(range(d), 2)
                    if (e+powers[i]+powers[j]) % p == 0}
            if hits:
                classes.setdefault(d, set()).update(hits)
    return classes


def possible(classes, s, t):
    return any(tuple(sorted((s % d, t % d))) in hits for d, hits in classes.items())


def verify_cover(e, taps, normalized=False):
    classes = {a: forbidden_classes(e, a, normalized) for a in taps}
    period = lcm(*(d for bounds in classes.values() for d in bounds))
    full_row = (1 << period) - 1
    uncovered = [full_row] * period
    for bounds in classes.values():
        bad = [0] * period
        for d, hits in bounds.items():
            # Bit t of row s records failure at (s,t). Repeat residues modulo d.
            repeat = full_row // ((1 << d) - 1)
            residues = [0] * d
            for i, j in hits:
                residues[i] |= repeat << j
                residues[j] |= repeat << i
            for s in range(period):
                bad[s] |= residues[s % d]
        uncovered = [old & new for old, new in zip(uncovered, bad)]
    for s, row in enumerate(uncovered):
        if row:
            t = (row & -row).bit_length() - 1
            raise ArithmeticError(f"no certified tap for e={e}, s={s}, t={t}")
    label = "coprime taps" if normalized else "taps"
    print(f"e={e}, {label} {taps}, all {period*(period+1)//2} unordered classes modulo {period} covered")
    for s, t in combinations_with_replacement(range(1, 10), 2):
        n = e + (1 << s) + (1 << t)
        for a, bounds in classes.items():
            if a >= n or possible(bounds, s, t):
                continue
            g = gcd(n, a)
            if (normalized and g != 1) or pair_and_triple_counts(n//g, a//g) != (0, 0):
                raise ArithmeticError(f"direct trinomial gcd disagrees at n={n}, a={a}")


if __name__ == "__main__":
    for offset, taps in TAPS.items():
        verify_cover(offset, taps)
    for offset, taps in NORMALIZED_TAPS.items():
        verify_cover(offset, taps, normalized=True)
    largest_tap = max(max(taps) for taps in NORMALIZED_TAPS.values())
    for n in range(5, largest_tap+1):
        works = any(gcd(n, a) == 1 and pair_and_triple_counts(n, a) == (0, 0)
                    for a in range(1, n))
        if works != (n != 8):
            raise ArithmeticError(f"unexpected small-degree result at n={n}")
    print(f"Small degrees 5 through {largest_tap} verified, with the single trinomial exception 8.")
