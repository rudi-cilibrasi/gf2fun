"""Check the finite subfield exclusions left by the square of the translated product."""

import argparse
import os
import subprocess
from itertools import combinations
from math import gcd

from flint import fmpz

from check_cubed_parity import X, polynomial, reciprocal
from check_dyadic_scalar_lifts import product
from check_odd_scalar_splits import check_archived_counts, read_archive
from check_power_orbit_collisions import root_order
from check_trinomial_subfield_pairs import prime_divisors


SCALARS = ((3, 7), (5, 31), (9, 73))
SMALL_31 = {5: {(2,), (1, 2, 3), (1, 2, 4)}, 10: {(1, 3, 8), (2, 4, 5)}, 15: set(), 20: set()}


def check_remaining(backend):
    archive = read_archive()
    totals = []
    for s, a in SCALARS:
        row = []
        for parity in (0, 1):
            cases = supports = 0
            for t in range(s+1, (s+1)**3//s+1):
                if t % 2 != parity or gcd(s, t) > 1 or 9*s > 4*t or 3*a > s*t:
                    continue
                key = (s, t, a)
                result = subprocess.run([backend, *map(str, key)], text=True, capture_output=True,
                                        env=dict(os.environ, OMP_NUM_THREADS='1'), check=True)
                counts = tuple(map(int, result.stdout.split()))
                if (len(counts) != 6 or counts[-1] or counts[:2] != check_archived_counts(s*t, a)
                        or (parity and counts != archive[key])):
                    raise ArithmeticError(f"incorrect product census at {key}")
                cases += 1
                supports += counts[1]
            row.append((cases, supports))
        totals.append(row)
        print(f"Scalar degree {s}, order {a}, (cases, supports) for even and odd partners: {row}.")
    if totals != [[(5, 4376), (5, 4072)], [(9, 12276), (11, 23328)], [(29, 85426), (29, 128232)]]:
        raise ArithmeticError("the finite square-bound census changed")


def check_square_identity():
    """Multiply the twists explicitly over three binary extension fields."""
    for (s, a), field in zip(SCALARS, (0b1011, 0b100101, 0b1000000011)):
        powers = [1]
        for _ in range(1, a):
            powers.append(product(powers[-1], 2, field))
        if len(set(powers)) != a or product(powers[-1], 2, field) != 1:
            raise ArithmeticError("incorrect scalar group")
        def twist_product(support, shifts):
            p = {0: 1}
            for k in shifts:
                q = {}
                for i in support:
                    coeff = powers[-k*i % a]
                    for j, c in p.items():
                        q[i+j] = q.get(i+j, 0) ^ product(coeff, c, field)
                p = {j: c for j, c in q.items() if c}
            if set(p.values()) != {1}:
                raise ArithmeticError("the Frobenius product did not descend")
            return tuple(sorted(p))
        seen = set()
        for k in range(1, a):
            if k in seen:
                continue
            orbit = [k*2**j % a for j in range(s)]
            seen.update(orbit)
            f = twist_product((0, 1, 2), orbit)
            if f[-1] != 2*s or not polynomial(f).is_irreducible():
                raise ArithmeticError("the explicit split root has incorrect degree")
            if any(i % 2 for i in twist_product(f, [0, *orbit])):
                raise ArithmeticError("the translated product is not a square")
    print("Direct field multiplication verified the square identity at scalar orders 7, 31 and 73.")


def check_small_partners():
    for n, expected in SMALL_31.items():
        found = set()
        m = n // 5
        for size in (1, 3):
            for taps in combinations(range(1, n), size):
                s = (0, *taps, n)
                if s > reciprocal(s):
                    continue
                f = polynomial(s)
                if f.is_irreducible() and X.pow_mod(31*(2**m-1), f) == 1:
                    if root_order(f) != 31*(2**m-1):
                        raise ArithmeticError(f"unexpected order at {s}")
                    found.add(taps)
        if found != expected:
            raise ArithmeticError(f"incorrect small 31st-power exceptions at degree {n}")
    print("Verified all small normalized exceptions to the 31st-power degree formula.")


def predicted_31_degree(s):
    g = gcd(*s)
    if g % 31 == 0:
        return s[-1] // 31
    base = tuple(e//g for e in s)
    if base[1:-1] in SMALL_31.get(base[-1], set()):
        return s[-1] // 5
    return s[-1]


def check_degree(s):
    f = polynomial(s)
    degree = predicted_31_degree(s)
    y = X.pow_mod(31, f)
    if (y.pow_mod(2**degree, f) != y
            or any(y.pow_mod(2**(degree//p), f) == y for p in prime_divisors(degree))):
        raise ArithmeticError(f"incorrect field degree at {s}")


def check_31_powers(limit):
    count = drops = 0
    for n in range(2, limit+1):
        for size in (1, 3):
            for taps in combinations(range(1, n), size):
                s = (0, *taps, n)
                if s <= reciprocal(s) and polynomial(s).is_irreducible():
                    check_degree(s)
                    count += 1
                    drops += predicted_31_degree(s) < n
    for n in (5, 10):
        for taps in SMALL_31[n]:
            for g in ((31,) if n == 5 else (3, 9, 31, 93)):
                s = tuple(e*g for e in (0, *taps, n))
                f = polynomial(s)
                order = (31 if n == 5 else 93)*g
                if (not f.is_irreducible() or X.pow_mod(order, f) != 1
                        or any(X.pow_mod(order//p, f) == 1 for p in prime_divisors(order))):
                    raise ArithmeticError(f"incorrect order for dilation {s}")
                check_degree(s)
    print(f"Direct 31st-power tests through degree {limit}: {count} irreducible reciprocal "
          f"classes and {drops} degree drops. Verified the indicated dilations.")


def check_large_example():
    p, q = 10007, 100170097
    if (not fmpz(p).is_prime() or not fmpz(q).is_prime() or p*q != 1002402160679
            or p*q <= (p+1)**3 or (q-1) % p == 0):
        raise ArithmeticError("invalid full-degree-prime example")
    print(f"The degree bound forces a prime of binary degree {p*q} at {(p, q)}.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--products', required=True, help='compiled scripts/check_scalar_pair_products.cpp')
    parser.add_argument('--through', type=int, default=48, help='degree for independent 31st-power tests')
    args = parser.parse_args()
    if args.through < 2:
        parser.error('use a degree of at least two')
    check_remaining(args.products)
    check_square_identity()
    check_small_partners()
    check_31_powers(args.through)
    check_large_example()
