"""Check the two degree-1229 root coordinates and exhaust their defining families."""

from itertools import combinations
from math import gcd

from flint import fmpz, nmod_poly

from check_degree_1229 import GROUP, N, check_known_order
from check_factor_base import modulus
from period_coordinate import mask_of


X = nmod_poly([0, 1], 2)
QUADRATIC_TAPS = (163, 533, 1066)
FROBENIUS_TAPS = (256, 461, 922)


def small_factors():
    """A polynomial divisible by every binary irreducible of degree at most eight."""
    product = X**2 + X
    for degree in range(2, 9):
        split = X**(1 << degree) + X
        product *= split // split.gcd(product)
    return product


def irreducible_candidate(taps, small):
    f = modulus(N, taps)
    # N is prime and the endpoints and odd weight exclude both linear factors.
    return f.gcd(small) == 1 and X.pow_mod(1 << N, f) == X


def scan_trinomial_presentations(small):
    count, matches = 0, []
    # For d a power of two >= 8, Swan's theorem excludes irreducible trinomials.
    for d in (2, 4):
        for b in range(1, d):
            p = X**d + X**b + 1
            if p.factor()[1] != [(p, 1)]:
                continue
            for u in range(1, (N - 1) // d + 1):
                v = N - d*u
                taps = tuple(sorted((b*u, d*u, v)))
                if len(set(taps)) != 3:
                    continue
                count += 1
                if irreducible_candidate(taps, small):
                    matches.append((d, b, u, v))
    if count != 1228 or matches != [(2, 1, 533, 163)]:
        raise ArithmeticError(f"unexpected quadratic-value census: {count}, {matches}")
    print(f"Checked {count} presentations. The unique irreducible has d=2, b=1, u=533, v=163.")


def scan_frobenius_relations(small):
    q, t = 256, 5
    matches = set()
    supports = set()
    for start in range(-2, 1):
        residues = {(start + offset) % q for offset in range(3)}
        if not {0, t*N % q} <= residues:
            continue
        taps = [i for i in range(1, N) if t*i % q in residues]
        supports.update(combinations(taps, 3))
    for taps in sorted(supports):
        if irreducible_candidate(taps, small):
            matches.add(taps)
    reciprocal = tuple(N - i for i in reversed(FROBENIUS_TAPS))
    if matches != {FROBENIUS_TAPS, reciprocal}:
        raise ArithmeticError(f"unexpected Frobenius census: {sorted(matches)}")
    print(f"Checked {len(supports)} supports at q=256 and t=5. One reciprocal pair is irreducible.")


def inverse(value, f):
    divisor, coefficient, _ = value.xgcd(f)
    if divisor != 1:
        raise ArithmeticError("nonunit in the proposed coordinate")
    return coefficient % f


def quadratic_minpoly(u, v):
    """Clear the denominator in the Dickson identity of index v."""
    previous, current = 0*X, X**0
    square = (1 + X)**2
    for _ in range(1, v):
        previous, current = current, current + square*previous
    return X**u * current + (1 + X)**v * (1 + X**(2*u))


def check_coordinates():
    f = modulus(N, QUADRATIC_TAPS)
    check_known_order(f)
    a = inverse(1 + X**533, f)
    ratio = (a + 1) * inverse(a, f) % f
    quadratic = (a**2 + a + 1) % f
    if ratio != X**533 or quadratic != X**163:
        raise ArithmeticError("the linear ratio or quadratic value has the wrong logarithm")
    g = (X + 1)**163 + X**163 * (X**2 + X + 1)**533
    if g.degree() != N or g.compose_mod(a, f) != 0 or X.pow_mod(1 << N, g) != X or g.gcd(X**2+X) != 1:
        raise ArithmeticError("the minimal polynomial of the fractional linear coordinate failed")
    r = ratio.pow_mod(63, f) * inverse(quadratic, f).pow_mod(206, f) % f
    if r != X or any(gcd(GROUP, k) != 1 for k in (163, 533)):
        raise ArithmeticError("the subgroup generators failed the reverse change of coordinates")
    h = quadratic_minpoly(533, 163)
    if h.degree() != N or mask_of(h).bit_count() != 51 or h.compose_mod(quadratic, f) != 0:
        raise ArithmeticError("the 51-term minimal polynomial of the quadratic value failed")

    g = modulus(N, FROBENIUS_TAPS)
    check_known_order(g)
    z = X.pow_mod(pow(5, -1, GROUP), g)
    y = z.pow_mod(256, g)
    relation = (y.pow_mod(18, g) * z**2 + (y.pow_mod(9, g) + y.pow_mod(24, g))*z + 1
                + y.pow_mod(5, g))
    if z.pow_mod(5, g) != X or relation % g != 0:
        raise ArithmeticError("the quadratic Frobenius equation failed")
    print("Both coordinates and the four known prime projections and extra power for each root passed.")


if __name__ == "__main__":
    if not fmpz(N).is_prime():
        raise ArithmeticError("the Rabin test here requires a prime degree")
    check_coordinates()
    small = small_factors()
    scan_trinomial_presentations(small)
    scan_frobenius_relations(small)
