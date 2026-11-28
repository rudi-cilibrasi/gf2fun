"""Find every odd-degree primitive pentanomial with sparse third and ninth powers of its roots."""

import argparse
from collections import Counter
from itertools import combinations, product
from math import gcd, prod

from flint import fmpz
from check_cubed_parity import X, polynomial, reciprocal
from check_cubed_supports import TEMPLATES, classify, cube_support, cubic_terms


def three_sparse(support):
    first = cube_support(support)
    return support[-1] % 2 == 1 and len(first) in (3, 5) and len(cube_support(first)) in (3, 5)


def collision_supports(shape, residues, *, skip_multiples_of_nine=False):
    """Two-parameter sources for which a collision makes the ninth power sparse."""
    r, s = residues
    first = cubic_terms(shape, [(i*r+j*s) % 3 for i, j in shape])
    found = set()
    for a, b in product(range(r % 3, 9, 3), range(s % 3, 9, 3)):
        labels = [((i*a+j*b)//3) % 3 for i, j in first]
        second = cubic_terms(first, labels)
        if skip_multiples_of_nine and a == 0:
            if len(second) != 5:
                raise ArithmeticError("unexpected ninth-power image of a mod-nine trinomial pair")
            continue
        if len(second) <= 5:
            raise ArithmeticError(f"generic sparse family at residues {(a, b)}")
        for (i, j), (k, l) in combinations(second, 2):
            scale = gcd(j-l, k-i)
            # The primitive solutions of (i-k)u+(j-l)v=0 differ only by sign.
            for sign in (1, -1):
                u, v = sign*((j-l)//scale), sign*((k-i)//scale)
                if u % 9 != a or v % 9 != b:
                    continue
                exponents = sorted({h*u+t*v for h, t in shape})
                if len(exponents) != len(shape):
                    continue
                support = tuple(x-exponents[0] for x in exponents)
                if three_sparse(support):
                    found.update((support, reciprocal(support)))
    return found


def primitive(f, n):
    order = 2**n-1
    factors = [(int(p), e) for p, e in fmpz(order).factor()]
    if prod(p**e for p, e in factors) != order or not all(fmpz(p).is_prime() for p, _ in factors):
        raise ArithmeticError(f"incomplete group factorization in degree {n}")
    return (f.is_irreducible() and X.pow_mod(order, f) == 1
            and all(X.pow_mod(order//p, f) != 1 for p, _ in factors))


def small_runs(n):
    sparse = {(0, *taps, n) for k in (1, 3) for taps in combinations(range(1, n), k)
              if primitive(polynomial((0, *taps, n)), n)}
    histogram = Counter()
    for source in sparse:
        current, seen = source, set()
        while current in sparse:
            if current in seen:
                raise ArithmeticError(f"unexpected all-sparse cycle in degree {n}")
            seen.add(current)
            current = cube_support(current)
        histogram[len(seen)] += 1
    return histogram


def check_signed_orders():
    for a in range(4):
        step = 7**a
        for tap in (step, 2 * step):
            s = (0, tap, 3 * step)
            f = polynomial(s)
            order = 7 * step
            if (not f.is_irreducible() or X.pow_mod(order, f) != 1 or X.pow_mod(step, f) == 1
                    or cube_support(s) != reciprocal(s)):
                raise ArithmeticError(f"signed cube exception failed at {s}")
    examples = [(3121, 1123561, 2917, -1), (3359, 6719, 104, 1),
                (26591, 7498663, 260, -1), (26731, 12189337, 21556, -1)]
    for n, p, j, sign in examples:
        if (not fmpz(n).is_prime() or not fmpz(p).is_prime() or pow(2, n, p) != 1
                or pow(2, j, p) != (sign * 3) % p):
            raise ArithmeticError(f"signed Frobenius congruence failed for degree {n} and order {p}")
        print(f"Degree {n}, excluded prime order {p}, 2^{j} equals {sign * 3} modulo {p}.")


def audit():
    candidates = {s for s in classify() if three_sparse(s)}
    for shape, residues in TEMPLATES:
        # The extrema of {0,u,2u,v,2v} occur among {0,2u,2v}. Its span is even.
        if residues == (1, 1):
            continue
        candidates.update(collision_supports(shape, residues))
    counts = Counter(s[-1] for s in candidates)
    if counts != {5: 4, 7: 10, 9: 14, 11: 10, 13: 2}:
        raise ArithmeticError(f"unexpected ninth-power exceptional degrees: {counts}")
    # A direct search across all supports in the exceptional degrees checks both directions.
    direct = {(0, *t, n) for n in range(5, 14, 2) for t in combinations(range(1, n), 3)
              if gcd(*t, n) == 1 and three_sparse((0, *t, n))}
    if direct != candidates:
        raise ArithmeticError("the linear collision list differs from the direct search")
    irreducibles = {s for s in candidates if polynomial(s).is_irreducible()}
    primitive_sources = {s for s in irreducibles if primitive(polynomial(s), s[-1])}
    if len(irreducibles) != 18 or Counter(s[-1] for s in primitive_sources) != {5: 4, 7: 4, 11: 4}:
        raise ArithmeticError("the irreducible or primitive census changed")
    if any(cube_support(s) in (s, reciprocal(s)) for s in irreducibles):
        raise ArithmeticError("a normalized pentanomial has a signed Frobenius cube")
    for s in primitive_sources:
        first, second = cube_support(s), cube_support(cube_support(s))
        f = polynomial(s)
        for t, k in ((first, 3), (second, 9)):
            if not primitive(polynomial(t), s[-1]) or polynomial(t).compose_mod(X**k, f) != 0:
                raise ArithmeticError(f"the power-{k} minimal polynomial failed at {s}")

    # A trinomial with a pair equal modulo three can be translated to 1+U+V.
    triangle = ((0, 0), (1, 0), (0, 1))
    exceptional_trinomials = collision_supports(triangle, (0, 1), skip_multiples_of_nine=True)
    if exceptional_trinomials != {(0, 1, 3), (0, 2, 3), (0, 2, 5), (0, 3, 5), (0, 1, 7), (0, 6, 7)}:
        raise ArithmeticError("unexpected trinomial exceptions")
    s = (0, 9, 23)
    if not primitive(polynomial(s), 23):
        raise ArithmeticError("the degree-23 trinomial is imprimitive")
    weights = []
    for _ in range(4):
        weights.append(len(s))
        s = cube_support(s)
    if weights != [3, 5, 5, 7]:
        raise ArithmeticError("incorrect degree-23 cubing sequence")
    histograms = {n: small_runs(n) for n in (7, 9, 11)}
    if histograms != {7: {1: 4, 2: 4, 3: 4, 4: 2}, 9: {1: 10, 2: 6, 3: 2},
                      11: {1: 32, 2: 8, 3: 4, 4: 2}}:
        raise ArithmeticError("unexpected small-degree run lengths")
    return candidates, primitive_sources


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="show all primitive sources and their two cube images")
    parser.add_argument("--signed-orders", action="store_true", help="check the dilated exceptions and excluded subgroups")
    args = parser.parse_args()
    candidates, primitive_sources = audit()
    print(f"{len(candidates)} normalized odd-degree pentanomials have sparse third and ninth powers.")
    print("18 are irreducible, of which 12 are primitive. The primitive degrees are 5, 7, and 11, four in each.")
    print("Beyond degree 11, a three-term source needs a pair of exponents equal modulo nine.")
    print("Four consecutive sparse iterates are impossible for odd primitive degrees above 11.")
    print("Degree 23 attains three, with successive weights 3, 5, 5, 7.")
    print("For odd degrees at least seven the sharp bound is four, attained only in degrees seven and eleven.")
    if args.signed_orders:
        check_signed_orders()
    if args.list:
        for s in sorted(primitive_sources, key=lambda t: (t[-1], t)):
            print(*s, "->", *cube_support(s), "->", *cube_support(cube_support(s)))
