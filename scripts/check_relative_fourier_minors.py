"""Check the four determinant coefficients for short triples of span at most 12.

Run with uv run --no-project --with python-flint==0.9.0 python
scripts/check_relative_fourier_minors.py.
"""

from itertools import combinations, permutations
from math import gcd

from flint import fmpz_poly


def grid_coefficients(middle, span):
    """Expand the collision product in four row variables, truncating at degree six in each."""
    x = fmpz_poly([0, 1])
    columns = (0, middle, span, x)
    zero = fmpz_poly([])
    terms = {(0, 0, 0, 0): fmpz_poly([1])}
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
                if degrees[r] == 6:
                    continue
                exponent = list(degrees)
                exponent[r] += 1
                key = tuple(exponent)
                product[key] = product.get(key, zero) + multiplier * coefficient
        terms = product
    expected = {tuple(5 if r == s else 6 for r in range(4)) for s in range(4)}
    assert terms.keys() == expected
    return [terms[key] for key in sorted(expected)]


def obstruction(middle, span):
    """Any prime admitting simultaneous vanishing at a fourth distinct column divides this gcd."""
    x = fmpz_poly([0, 1])
    reduced = []
    for coefficient in grid_coefficients(middle, span):
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


def main():
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


if __name__ == "__main__":
    main()
