"""Certify trinomial root-product tests for n = e + 2^s + 2^t. Requires python-flint."""

from functools import cache
from itertools import combinations_with_replacement
from math import gcd, lcm

from flint import nmod_mpoly_ctx, nmod_poly

from check_trinomial_triples import pair_and_triple_counts


X = nmod_poly([0, 1], 2)
SYMMETRIC = nmod_mpoly_ctx.get(("S", "P"), 2)
S, P = SYMMETRIC.gens()
TAPS = {1: (3, 4, 5, 7), 2: (3, 7, 11)}


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


def possible_classes(e, a):
    """Necessary residue pairs for a product-one triple, grouped by factor degree."""
    classes = {}
    for modulus, _ in commutation_polynomial(e, a).factor()[1]:
        degree = modulus.degree()
        if degree == 1:  # u and u+1 are both nonzero at every admissible point.
            continue
        phi = (1+X).pow_mod((1 << degree)-2, modulus)
        orbits = [frobenius_orbit(point, modulus) for point in (X, phi)]
        checks = [(point**e % modulus, (1+point)**a % modulus, orbit)
                  for point, orbit in zip((X, phi), orbits)]
        hits = {(i, j) for i, j in combinations_with_replacement(range(degree), 2)
                if all(base * orbit[i] * orbit[j] % modulus == target
                       for base, target, orbit in checks)}
        if hits:
            classes.setdefault(degree, set()).update(hits)
    return classes


def possible(classes, s, t):
    return any(tuple(sorted((s % d, t % d))) in hits for d, hits in classes.items())


def verify_cover(e, taps):
    classes = {a: possible_classes(e, a) for a in taps}
    period = lcm(*(d for bounds in classes.values() for d in bounds))
    for s, t in combinations_with_replacement(range(period), 2):
        if all(possible(bounds, s, t) for bounds in classes.values()):
            raise ArithmeticError(f"no certified tap for e={e}, s={s}, t={t}")
    print(f"e={e}, taps {taps}, all {period*(period+1)//2} unordered classes modulo {period} covered")
    for s, t in combinations_with_replacement(range(1, 10), 2):
        n = e + (1 << s) + (1 << t)
        for a, bounds in classes.items():
            if a >= n or possible(bounds, s, t):
                continue
            g = gcd(n, a)
            if pair_and_triple_counts(n//g, a//g) != (0, 0):
                raise ArithmeticError(f"direct trinomial gcd disagrees at n={n}, a={a}")


if __name__ == "__main__":
    for offset, taps in TAPS.items():
        verify_cover(offset, taps)
