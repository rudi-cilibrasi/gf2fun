"""Certify trinomial root-product tests for degrees e + 2^s ± 2^t. Requires python-flint and SymPy."""

from functools import cache
from itertools import combinations_with_replacement, product
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


# (offset, sign, require coprimality, taps) for the signed three-power theorem.
SIGNED_TAPS = (
    (-1, 1, True, (2, 3, 4, 7)), (-2, 1, True, (1, 3, 7, 15)),
    (1, -1, True, (4, 6, 7, 8, 12)), (-1, -1, False, (5, 6, 7, 9, 11)),
    (2, -1, False, (5, 7, 9, 11, 13)), (-2, -1, False, (3, 5, 7, 11)),
)


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


def reduced_fraction(numerator, denominator):
    common = numerator.gcd(denominator)
    return numerator // common, denominator // common


def compose_fraction(outer, inner):
    num, den = inner
    degree = max(f.degree() for f in outer)

    def homogeneous(f):
        return sum((num**i * den**(degree-i)
                    for i, coefficient in enumerate(f.coeffs()) if coefficient), 0*X)

    return homogeneous(outer[0]), homogeneous(outer[1])


def commutation_polynomial(e, a, sign):
    """Annihilator for the two Frobenius images, independent of their positions."""
    if a < 1 or sign not in (-1, 1):
        raise ValueError("the inner exponent must be positive and the sign must be ±1")
    m = max(e, a)
    denominator = X**m * (X+1)**max(e-a, 0)
    product_num = X**(m-e) * (X+1)**(a+max(e-a, 0))
    translated_num = X**(m-a) * (X+1)**max(a-e, 0)
    if sign == -1:
        # b=P*c, 1+b=R*(1+c), for P=product_num/D and R=translated_num/D.
        difference = product_num + translated_num
        if difference.is_zero():
            raise ValueError(f"the two equations coincide at e={e}, a={a}")
        c = reduced_fraction(denominator + translated_num, difference)
        b = reduced_fraction(product_num*c[0], denominator*c[1])
        left_num, left_den = compose_fraction(b, c)
        right_num, right_den = compose_fraction(c, b)
        commutator = left_num*right_den + right_num*left_den
        if commutator.is_zero():
            raise ValueError(f"the rational maps commute identically at e={e}, a={a}")
        exceptional = (denominator+product_num).gcd(denominator+translated_num)
        return commutator * exceptional
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


def signed_power(value, exponent, modulus):
    if exponent < 0:
        return inverse(value, modulus).pow_mod(-exponent, modulus)
    return value.pow_mod(exponent, modulus)


@cache
def possible_classes(e, a, sign):
    """Necessary residue pairs for a product-one triple, grouped by factor degree."""
    classes = {}
    for modulus, _ in commutation_polynomial(e, a, sign).factor()[1]:
        degree = modulus.degree()
        if degree == 1:  # u and u+1 are both nonzero at every admissible point.
            continue
        orbit = frobenius_orbit(X, modulus)
        positions = {tuple(value.coeffs()): i for i, value in enumerate(orbit)}
        phi = inverse(1+X, modulus)
        translated = frobenius_orbit(phi, modulus)
        ratio = (1+X).pow_mod(a, modulus) * signed_power(X, -e, modulus) % modulus
        phi_ratio = (1+phi).pow_mod(a, modulus) * signed_power(phi, -e, modulus) % modulus
        hits = set()
        if sign == 1:
            for i, reciprocal_i in enumerate(frobenius_orbit(inverse(X, modulus), modulus)):
                partner = ratio * reciprocal_i % modulus
                j = positions.get(tuple(partner.coeffs()))
                if j is not None and i <= j and translated[i]*translated[j] % modulus == phi_ratio:
                    hits.add((i, j))
        else:
            for j, c in enumerate(orbit):
                i = positions.get(tuple((ratio*c % modulus).coeffs()))
                if i is not None and translated[i] == phi_ratio*translated[j] % modulus:
                    hits.add((i, j))
        if hits:
            classes.setdefault(degree, set()).update(hits)
    return classes


def forbidden_classes(e, a, sign, normalized):
    classes = {d: hits.copy() for d, hits in possible_classes(e, a, sign).items()}
    if normalized:
        for p in factorint(a):
            if p == 2:
                if e % 2 == 0:  # s,t are positive, so n has the parity of e.
                    classes.setdefault(1, set()).add((0, 0))
                continue
            d = int(n_order(2, p))
            powers = [pow(2, j, p) for j in range(d)]
            pairs = combinations_with_replacement(range(d), 2) if sign == 1 else product(range(d), repeat=2)
            hits = {(i, j) for i, j in pairs if (e+powers[i]+sign*powers[j]) % p == 0}
            if hits:
                classes.setdefault(d, set()).update(hits)
    return classes


def possible(classes, s, t, sign):
    for d, hits in classes.items():
        i, j = s % d, t % d
        if (i, j) in hits or (sign == 1 and (j, i) in hits):
            return True
    return False


def verify_cover(e, taps, normalized=False, sign=1):
    classes = {a: forbidden_classes(e, a, sign, normalized) for a in taps}
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
                if sign == 1:
                    residues[j] |= repeat << i
            for s in range(period):
                bad[s] |= residues[s % d]
        uncovered = [old & new for old, new in zip(uncovered, bad)]
    for s, row in enumerate(uncovered):
        if row:
            t = (row & -row).bit_length() - 1
            raise ArithmeticError(f"no certified tap for e={e}, s={s}, t={t}")
    label = "coprime taps" if normalized else "taps"
    if sign == 1:
        count = f"{period*(period+1)//2} unordered"
        samples = combinations_with_replacement(range(1, 10), 2)
    else:
        count = f"{period**2} ordered"
        samples = product(range(1, 10), repeat=2)
    print(f"e={e}, sign={sign:+}, {label} {taps}, all {count} classes modulo {period} covered")
    for s, t in samples:
        n = e + (1 << s) + sign*(1 << t)
        for a, bounds in classes.items():
            if a >= n or possible(bounds, s, t, sign):
                continue
            g = gcd(n, a)
            if (normalized and g != 1) or pair_and_triple_counts(n//g, a//g) != (0, 0):
                raise ArithmeticError(f"direct trinomial gcd disagrees at n={n}, a={a}")


def no_frobenius_orbit(period, shift):
    common = gcd(period, shift)
    return common % 2 == 1 and (period // common) % 3 != 0


def three_part(value):
    part = 1
    while value % 3 == 0:
        value //= 3
        part *= 3
    return part


def dyadic_minus_position(s, t):
    """Exponent position of a passing power-of-two tap for n=2^s-2^t-1."""
    if not 1 <= t <= s-2:
        raise ValueError("expected 1 ≤ t ≤ s-2")
    first, second = three_part(s), three_part(s-t)
    step = max(first, second)
    position = t if first >= second else 0
    if (s % 2 == 0 and (t-position) % 2 == 0) or ((s-t) % 2 == 0 and position % 2 == 0):
        position = position+step if position+step < s else position-step
    return position


def verify_dyadic_minus():
    for s in range(3, 101):
        for t in range(1, s-1):
            i = dyadic_minus_position(s, t)
            if not (0 <= i < s and no_frobenius_orbit(s, t-i) and no_frobenius_orbit(s-t, i)):
                raise ArithmeticError(f"invalid constructed tap position at s={s}, t={t}")
            if s <= 10:
                n = (1 << s) - (1 << t) - 1
                for i in range(s):
                    prediction = no_frobenius_orbit(s, t-i) and no_frobenius_orbit(s-t, i)
                    if prediction != (pair_and_triple_counts(n, 1 << i) == (0, 0)):
                        raise ArithmeticError(f"orbit criterion disagrees at s={s}, t={t}, i={i}")
    print("Dyadic choices through s=100 verified; every tap through s=10 agrees with the polynomial gcd.")


if __name__ == "__main__":
    for offset, taps in TAPS.items():
        verify_cover(offset, taps)
    for offset, taps in NORMALIZED_TAPS.items():
        verify_cover(offset, taps, normalized=True)
    for offset, sign, normalized, taps in SIGNED_TAPS:
        verify_cover(offset, taps, normalized=normalized, sign=sign)
    largest_tap = max(max(taps) for taps in NORMALIZED_TAPS.values())
    for n in range(5, largest_tap+1):
        works = any(gcd(n, a) == 1 and pair_and_triple_counts(n, a) == (0, 0)
                    for a in range(1, n))
        if works != (n != 8):
            raise ArithmeticError(f"unexpected small-degree result at n={n}")
    print(f"Small degrees 5 through {largest_tap} verified, with the single trinomial exception 8.")
    verify_dyadic_minus()
