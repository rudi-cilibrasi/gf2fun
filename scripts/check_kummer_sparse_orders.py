"""Check the five-column determinant isolation and count sparse prime dilations."""

from collections import Counter
from functools import cache
from itertools import combinations, permutations
from math import comb, gcd, isqrt


MULTIPLICITIES = ((4, 1), (3, 2), (3, 1, 1), (2, 2, 1), (2, 1, 1, 1))


@cache
def prime_divisors(value):
    """Prime divisors of a positive integer from an integral determinant certificate."""
    if value < 1:
        raise ValueError("expected a nonzero certificate integer")
    divisors = set()
    for p in range(2, isqrt(value) + 1):
        if value % p == 0:
            divisors.add(p)
            while value % p == 0:
                value //= p
    if value > 1:
        divisors.add(value)
    return divisors


def direction(vector, prime):
    """Canonical projective coordinates over the rationals or over the prime field."""
    if prime:
        pivot = next((v % prime for v in vector if v % prime), 0)
        inverse = pow(pivot, -1, prime) if pivot else 0
        return tuple(v * inverse % prime for v in vector)
    content = gcd(*vector)
    if not content:
        return tuple(vector)
    if next(v for v in vector if v) < 0:
        content = -content
    return tuple(v // content for v in vector)


def dot(left, right):
    return sum(a*b for a, b in zip(left, right))


def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])


def row_charts(sizes, weights):
    """For each consecutive-block assignment, compare with each different labelled assignment."""
    labels = tuple(i for i, size in enumerate(sizes) for _ in range(size))
    # Translation sets the first residue to zero, so its coordinate can be omitted.
    sums = {way: tuple(sum(weights[row] for row, label in enumerate(way) if label == group)
                       for group in range(1, len(sizes)))
            for way in sorted(set(permutations(labels)))}
    for order in permutations(range(len(sizes))):
        target = tuple(i for i in order for _ in range(sizes[i]))
        yield [tuple(a-b for a, b in zip(sums[target], vector))
               for way, vector in sums.items() if way != target]


@cache
def collision_forms(sizes, weights=(1, 2, 4, 8, 16)):
    return list(row_charts(sizes, weights))


def equal_residue_hyperplanes(dimension, prime):
    basis = [(0,)*dimension] + [tuple(int(i == j) for j in range(dimension))
                                for i in range(dimension)]
    return {direction(tuple(x-y for x, y in zip(a, b)), prime)
            for a, b in combinations(basis, 2)}


def check_layouts(sizes, prime=0):
    """Check coverage and, over Q, return all primes that can change this proof."""
    dimension = len(sizes)-1
    exceptional = set()
    charts = []
    for raw in collision_forms(sizes):
        if not prime:
            for form in raw:
                exceptional.update(prime_divisors(gcd(*form)))
        forms = {direction(form, prime) for form in raw}
        if (0,)*dimension not in forms:
            charts.append(forms)
    if not charts:
        raise ArithmeticError(f"no nondegenerate row assignment for {sizes} modulo {prime}")

    points = set()
    forbidden = equal_residue_hyperplanes(dimension, prime)
    if dimension == 1:
        points.add((1,))
    else:
        for normal in charts[0]:
            if normal in forbidden:
                continue
            if dimension == 2:
                points.add(direction((-normal[1], normal[0]), prime))
                continue
            # Any surviving point on this line must meet a line of the second chart.
            other = next((chart for chart in charts if normal not in chart), None)
            if other is None:
                raise ArithmeticError(f"unresolved line {normal} for {sizes} modulo {prime}")
            for second in other:
                point = cross(normal, second)
                if not prime:
                    exceptional.update(prime_divisors(gcd(*point)))
                points.add(direction(point, prime))

    for point in sorted(points):
        if len({0, *point}) < len(sizes):
            continue
        for chart in charts:
            values = [dot(point, normal) for normal in chart]
            if all(value % prime if prime else value for value in values):
                if not prime:
                    for value in values:
                        exceptional.update(prime_divisors(abs(value)))
                break
        else:
            raise ArithmeticError(f"unresolved residues {point} for {sizes} modulo {prime}")
    return exceptional


def check_isolation():
    for sizes in MULTIPLICITIES:
        exceptional = check_layouts(sizes)
        remaining = sorted(p for p in exceptional if p >= 37)
        for prime in remaining:
            check_layouts(sizes, prime)
        print(f"Multiplicities {sizes}: {len(remaining)} primes at least 37 "
              f"from the rational calculation, all verified.", flush=True)

    # In a degree-eleven extension the steps 1, 2 and 3 all generate Frobenius.
    for sizes in MULTIPLICITIES:
        # Translation and scaling set the first two labelled residues to 0 and 1.
        points = [(1, *tail) for tail in permutations(range(2, 23), len(sizes)-2)]
        for step in (1, 2, 3):
            weights = tuple(2**(step*i) for i in range(5))
            charts = collision_forms(sizes, weights)
            points = [point for point in points
                      if not any(all(dot(h, point) % 23 for h in chart) for chart in charts)]
        if points:
            raise ArithmeticError(f"unresolved degree-eleven residues modulo 23: {points[0]}")
    print("Steps 1, 2 and 3 cover every residue pattern modulo 23 at relative degree 11.")


def check_second_level(p, q, taps, base_order):
    """Prove every root of the expanded polynomial has the asserted order and degree."""
    from flint import fmpz, nmod_poly

    degree = p*q**2
    order = base_order*q**2
    if pow(2, degree, order) != 1 or any(pow(2, degree//d, order) == 1 for d in (p, q)):
        raise ArithmeticError(f"incorrect binary degree for order {order}")
    coefficients = [0]*(degree+1)
    for exponent in (0, *taps, p):
        coefficients[exponent*q**2] = 1
    f = nmod_poly(coefficients, 2)
    x = nmod_poly([0, 1], 2)
    if x.pow_mod(order, f) != 1:
        raise ArithmeticError(f"incorrect full power for {taps} in degree {degree}")
    for prime, _ in fmpz(order).factor():
        if (x.pow_mod(order//int(prime), f)-1).gcd(f) != 1:
            raise ArithmeticError(f"a root fails the {prime} test in degree {degree}")


def check_trinomial_orders(limit):
    """Recover the proper-degree part of each field order independently by gcd."""
    from check_factor_base import irreducible, modulus, polynomial

    x = polynomial(2)
    tested = exceptions = 0
    for n in range(3, limit+1, 2):
        factors = sorted(prime_divisors(n))
        if len(factors) != 2:
            continue
        p, q = factors
        proper = (2**(n//p)-1)*(2**(n//q)-1)
        remaining = 2**n-1
        while (part := gcd(remaining, proper)) > 1:
            remaining //= part
        exponent = (2**n-1)//remaining
        for k in range(1, n//2+1):
            f = modulus(n, (k,))
            if not irreducible(f):
                continue
            missing = x.pow_mod(exponent, f) == 1
            if missing != (k % q == 0):
                raise ArithmeticError(f"wrong full-degree prime test for n={n}, k={k}")
            tested += 1
            exceptions += missing
    print(f"Through {limit}, {tested} irreducible trinomial pairs in odd two-prime degrees "
          f"give exactly {exceptions} exceptions to the full-degree prime test.")


def check_counts():
    import csv
    import gzip
    from flint import fmpz
    from check_factor_base import DATA, irreducible, modulus, polynomial

    x = polynomial(2)
    parameters = {3: [7], 5: [31], 7: [127], 11: [23, 89], 23: [47]}
    small = [(p, q) for p in range(3, 36, 2) if fmpz(p).is_prime()
             for q in range(p+2, 1280//p + 1, 2) if fmpz(q).is_prime() and pow(2, p, q) == 1]
    if small != [(p, q) for p, primes in parameters.items() for q in primes]:
        raise ArithmeticError("incorrect set of exceptional degrees through 1280")
    expected = {(21, 49): 1, (155, 961): 3, (253, 47081): 23, (889, 16129): 7,
                (979, 7921): 1, (979, 182183): 23, (1081, 394264529): 148}
    direct_degrees = {21, 155, 253, 889, 979}
    predicted = []
    counts = Counter()
    for p, primes in parameters.items():
        group = 2**p - 1
        factors = [int(factor) for factor, _ in fmpz(group).factor()]
        for weight in (1, 3):
            for taps in combinations(range(1, p), weight):
                if taps > tuple(p-j for j in reversed(taps)):
                    continue
                f = modulus(p, taps)
                if not irreducible(f):
                    continue
                order = group
                for factor in factors:
                    while order % factor == 0 and x.pow_mod(order//factor, f) == 1:
                        order //= factor
                for q in primes:
                    if x.pow_mod(group//q, f) != 1:
                        counts[p*q, q*order] += 1
                        if p*q in direct_degrees:
                            predicted.append((p*q, tuple(q*j for j in taps), q*order))
                        if (p, q) in ((7, 127), (11, 23)):
                            check_second_level(p, q, taps, order)
    if counts != expected:
        raise ArithmeticError(f"incorrect small-degree dilation census {counts}")
    with (DATA / "semiprime-direct-exceptions.csv").open(newline="") as source:
        archive = [(int(row["degree"]), tuple(map(int, row["taps"].split())), int(row["root_order"]))
                   for row in csv.DictReader(source)]
    if archive != sorted(predicted):
        raise ArithmeticError("the direct NTL census disagrees with the predicted exceptional supports")
    for n, taps, order in archive:
        f = modulus(n, taps)
        if (not irreducible(f) or x.pow_mod(order, f) != 1 or
                any(x.pow_mod(order//int(r), f) == 1 for r, _ in fmpz(order).factor())):
            raise ArithmeticError(f"incorrect expanded polynomial or order at degree {n}, taps {taps}")
    print(f"The {len(archive)} exceptional pairs from five direct NTL enumerations agree "
          "with the base-field prediction and have the recorded orders in the expanded fields.")
    with gzip.open(DATA / "degree-1229-irreducible-supports.csv.gz", "rt", newline="") as source:
        masks = Counter(int(row["missing_mask"]) for row in csv.DictReader(source))
    large = [2*sum(count for mask, count in masks.items() if not mask & bit) for bit in (1, 2)]
    if masks != {0: 319572, 1: 5, 2: 6} or large != [639156, 639154]:
        raise ArithmeticError(f"incorrect degree-1229 dilation counts {large}")
    for q, count, bits in zip((36871, 46703), large, ((74, 120, 165), (75, 122, 168))):
        if not fmpz(q).is_prime() or pow(2, 1229, q) != 1:
            raise ArithmeticError(f"{q} must be a prime divisor of the base field order")
        sizes = tuple((comb(1229*q**j-1, 3)-1).bit_length() for j in (1, 2, 3))
        if (count-1).bit_length() != 20 or sizes != bits:
            raise ArithmeticError("incorrect fixed-length support codes")
    print("Small reciprocal-pair counts and orders verified, including all lifted polynomials "
          "in degrees 5819 and 112903. "
          f"The two towers over degree 1229 have {large[0]} and {large[1]} exceptions per level.")


if __name__ == "__main__":
    check_isolation()
    check_counts()
    check_trinomial_orders(384)
