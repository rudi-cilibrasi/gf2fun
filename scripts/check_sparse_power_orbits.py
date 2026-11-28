"""Check the signed Frobenius orbits of the first three odd powers of a sparse root."""

from itertools import combinations
from math import lcm

from flint import fmpz

from check_cubed_parity import X, polynomial


def degree_bound(weight, a, b, sign):
    scale = lcm(a, b) * (2 if sign == -1 else 1)
    return scale ** (weight - 2)


def prime_degree_sieve():
    """A collision forces the root order to divide both integers in the gcd."""
    pairs = tuple(combinations((1, 3, 5), 2))
    max_degree = max(degree_bound(5, a, b, -1) for a, b in pairs)
    tests = 0
    maxima = {}
    for n in range(13, max_degree + 1, 2):
        if not fmpz(n).is_prime():
            continue
        full = (fmpz(1) << n) - 1
        powers = {v: fmpz(v)**n for v in (1, 3, 5)}
        for a, b in pairs:
            for sign in (1, -1):
                if n > degree_bound(5, a, b, sign):
                    continue
                common = int(full.gcd(powers[a] - sign * powers[b]))
                if common > 256 * n + 1:
                    raise ArithmeticError(f"unresolved common divisor {common} in degree {n}")
                key = a, b, sign
                maxima[key] = max(maxima.get(key, (0, 0)), (common, n))
                tests += 1
    return tests, maxima


def check_small_degrees():
    """Enumerate the actual Frobenius orbits of all three- and five-term irreducibles."""
    counts = {}
    for n in (3, 5, 7, 11):
        full = 2**n - 1
        count = 0
        for size in (1, 3):
            for taps in combinations(range(1, n), size):
                f = polynomial((0, *taps, n))
                if not f.is_irreducible():
                    continue
                count += 1
                powers = {e * 2**j % full for e in (1, -1, 3, -3, 5, -5) for j in range(n)}
                values = {tuple(map(int, X.pow_mod(e, f).coeffs())) for e in powers}
                expected = 2 * n if n == 3 else 6 * n
                if len(values) != expected:
                    raise ArithmeticError(f"wrong signed orbit count at {(0, *taps, n)}")
        counts[n] = count
    return counts


def check_excluded_orders():
    # Each equality a = 2^j * b rules out this entire subgroup for sparse irreducibles.
    rows = ((6067, 3118439, 3, 5), (47387, 42079657, 1, 7), (59921, 23489033, 3, 5))
    for n, prime, a, b in rows:
        if (not fmpz(n).is_prime() or not fmpz(prime).is_prime() or pow(2, n, prime) != 1
                or n <= degree_bound(5, a, b, 1)):
            raise ArithmeticError(f"incorrect subgroup example in degree {n}")
        value = b
        for j in range(n):
            if value == a:
                print(f"Degree {n}, excluded order {prime}: {a} = {b} * 2^{j} modulo {prime}.")
                break
            value = 2 * value % prime
        else:
            raise ArithmeticError(f"no power congruence for {prime}")


if __name__ == "__main__":
    tests, maxima = prime_degree_sieve()
    print(f"{tests} signed gcd tests in prime degrees from 13 through 27000.")
    for (a, b, sign), (common, n) in sorted(maxima.items()):
        print(f"Pair {a}, {b}, sign {sign}: largest gcd {common}, attained in degree {n}.")
    print(f"Direct sparse irreducible counts by degree: {check_small_degrees()}.")
    check_excluded_orders()
