"""Check short triples, four unrestricted columns, and rows of multiplicative order five.

Run with uv run --no-project --with python-flint==0.9.0 python
scripts/check_relative_fourier_minors.py.
"""

from collections import Counter
from itertools import combinations, permutations
from math import gcd

from flint import fmpz, fmpz_mpoly_ctx, fmpz_poly


def grid_coefficients(columns, cap):
    """Expand the collision product, keeping row exponents at most cap."""
    zero = columns[-1] * 0
    terms = {(0, 0, 0, 0): zero + 1}
    for perm in permutations(range(4)):
        moved = [r for r in range(4) if r != perm[r]]
        if not moved:
            continue
        if len(moved) == 2:
            # Distinct columns allow removal of the column difference from a transposition.
            form = [(moved[0], 1), (moved[1], -1)]
        else:
            form = [(r, columns[r] - columns[perm[r]]) for r in moved]
        product = {}
        for degrees, coefficient in terms.items():
            for r, multiplier in form:
                if degrees[r] == cap:
                    continue
                exponent = list(degrees)
                exponent[r] += 1
                key = tuple(exponent)
                product[key] = product.get(key, zero) + multiplier * coefficient
        terms = product
    return terms


def obstruction(middle, span):
    """Any prime admitting simultaneous vanishing at a fourth distinct column divides this gcd."""
    x = fmpz_poly([0, 1])
    reduced = []
    terms = grid_coefficients((0, middle, span, x), 6)
    expected = {tuple(5 if r == s else 6 for r in range(4)) for s in range(4)}
    assert terms.keys() == expected
    for coefficient in terms.values():
        assert coefficient
        for excluded in (0, middle, span):
            while coefficient(excluded) == 0:
                coefficient, remainder = divmod(coefficient, x - excluded)
                assert not remainder
        reduced.append(coefficient)
    bound = 0
    for first, second in combinations(reduced, 2):
        bound = gcd(bound, int(first.resultant(second)))
    assert bound > 0
    return bound


def check_short_triples():
    possible_primes = (2, 3, 5, 7, 11)
    seen = set()
    count = 0
    for span in range(2, 13):
        # Reflection of the triple interchanges middle and span - middle.
        for middle in range(1, span // 2 + 1):
            if gcd(middle, span) != 1:
                continue
            bound = obstruction(middle, span)
            divisors = []
            for prime in possible_primes:
                if bound % prime == 0:
                    divisors.append(prime)
                    while bound % prime == 0:
                        bound //= prime
            assert bound == 1, (middle, span, bound)
            seen.update(divisors)
            count += 1
            print(f"triple (0, {middle}, {span}): resultant gcd primes {divisors}")
    assert count == 23 and seen == set(possible_primes)
    print(f"Verified {count} triple shapes. Largest possible prime is {max(seen)}.")


def remove_small_primes(n):
    n = abs(int(n))
    assert n
    for prime in (2, 3, 5, 7):
        while n % prime == 0:
            n //= prime
    return n


def check_unrestricted_columns():
    """For four distinct columns, six coefficients suffice on a grid with eight row choices."""
    context = fmpz_mpoly_ctx.get(("a", "b"))
    a, b = context.gens()
    exponents = ((5, 6, 6, 6), (6, 5, 6, 6), (6, 6, 5, 6),
                 (5, 5, 6, 7), (5, 5, 7, 6), (5, 6, 5, 7))
    grid = grid_coefficients((0, 1, a, b), 7)

    def normalize(poly):
        assert poly
        for factor in (a, a-1, b, b-1, a-b):
            while not poly % factor:
                poly = poly // factor
        content = int(poly.content())
        return poly // (content // remove_small_primes(content))

    coefficients = [normalize(grid[e]) for e in exponents]
    resultants = []
    for i, j in ((0, 5), (1, 3), (2, 4), (3, 5)):
        eliminated = normalize(coefficients[i].resultant(coefficients[j], 1))
        terms = eliminated.to_dict()
        assert all(y == 0 for _, y in terms)
        resultants.append(fmpz_poly([terms.get((x, 0), 0) for x in range(eliminated.degrees()[0]+1)]))
    bounds = []
    bound = 0
    for polynomial in resultants[1:]:
        bound = remove_small_primes(gcd(bound, int(resultants[0].resultant(polynomial))))
        bounds.append(bound)
    assert bounds[1:] == [643, 1]
    print("Four unrestricted columns: verified eight row choices suffice in every prime characteristic above 7.")


def fifth_root_forms(row_powers):
    """A collision for columns (0,1,2,C) has the form A(U) C + B(U) = 0."""
    rows = [fmpz_poly([0]*e + [1]) for e in row_powers]
    fixed = (0, 1, 2, 0)
    for perm in permutations(range(4)):
        if sum(r != perm[r] for r in range(4)) < 3:
            continue
        a = rows[3] - rows[perm.index(3)]
        b = sum(u * (fixed[r] - fixed[perm[r]]) for r, u in enumerate(rows))
        yield a, b


def check_five_rows():
    phi = fmpz_poly([1]*5)
    first = list(fifth_root_forms((0, 1, 2, 3)))
    second = list(fifth_root_forms((0, 1, 3, 2)))
    conditions = [b for a, b in first if not a]
    conditions += [a * other_b - other_a * b
                   for a, b in first if a for other_a, other_b in second]
    norms = {abs(int(phi.resultant(poly))) for poly in conditions}
    assert len(conditions) == 257 and len(norms) == 20 and 0 not in norms
    exceptional = sorted({int(p) for n in norms for p, _ in fmpz(n).factor() if p % 5 == 1})
    assert exceptional == [11, 31, 41, 61, 71, 101, 131, 151, 181]
    for ell in exceptional:
        u = next(t for t in range(2, ell) if pow(t, 5, ell) == 1)
        rows = [pow(u, e, ell) for e in range(4)]
        for c in range(3, ell):
            sums = Counter(sum(r * s for r, s in zip(rows, assignment)) % ell
                           for assignment in permutations((0, 1, 2, c)))
            assert 1 in sums.values(), (ell, c)
    print("An order-five subgroup separates (0,1,2,c) for every prime length congruent to 1 modulo 5.")


if __name__ == "__main__":
    check_short_triples()
    check_unrestricted_columns()
    check_five_rows()
