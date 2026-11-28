"""Determine the field degree of the seventh power of every sparse irreducible binary root.

Compile scripts/power_orbit_collisions.cpp and pass its executable with --solver.
"""

import argparse
import tempfile
from itertools import combinations
from math import gcd

from check_cubed_parity import X, polynomial, reciprocal
from check_power_orbit_collisions import matching_supports, profiles, root_order
from check_trinomial_subfield_pairs import prime_divisors
from power_images import norm_pattern, power_characteristic


# A missing residue class in the power sums, up to reciprocation. The first
# two supports are the only irreducibles on the list.
TRACE_SUPPORTS = (
    (0, 1, 3), (0, 1, 2, 4, 6), (0, 1, 2, 4, 7), (0, 1, 3, 6, 8),
    (0, 2, 7, 8, 11), (0, 2, 7, 13, 16), (0, 4, 7, 14, 19),
    (0, 2, 14, 17, 21), (0, 4, 13, 14, 25),
)
EXCEPTION_DEGREES = {TRACE_SUPPORTS[0]: 1, TRACE_SUPPORTS[1]: 2}


def trace_profiles(backend):
    count = 0
    with tempfile.TemporaryFile(mode="w+") as source:
        for weight in (3, 5):
            for labels in profiles(14, weight):
                cofactor = norm_pattern(7, tuple(e % 7 for e in labels), omit_identity=True)
                # Multiply the six twists by the Euler derivative of the untwisted factor.
                numerator = set()
                for mix in cofactor:
                    for i, exponent in enumerate(labels):
                        if exponent % 2:
                            term = mix[:i] + (mix[i] + 1,) + mix[i+1:]
                            numerator.symmetric_difference_update((term,))
                for residue in (1, 6):
                    terms = [mix[1:] for mix in numerator
                             if sum(c * e for c, e in zip(mix, labels)) % 7 == residue]
                    # Both residues give the same unsigned list after taking reciprocals.
                    print(weight, 14, 1, *labels[1:], len(terms), file=source)
                    for term in terms:
                        print(*term, file=source)
                    count += 1
        supports = {s for _, s in matching_supports(source, backend)}
    expected = set(TRACE_SUPPORTS) | {reciprocal(s) for s in TRACE_SUPPORTS}
    if supports != expected:
        raise ArithmeticError("the trace elimination differs from the support list")
    for s in TRACE_SUPPORTS:
        f = polynomial(s)
        norm = polynomial(tuple(7 * e for e in power_characteristic(s, 7)))
        cofactor, remainder = divmod(norm, f)
        numerator = X * f.derivative() * cofactor
        if remainder or not any(all(not numerator[j] for j in range(t, numerator.degree()+1, 7))
                                for t in (1, 6)):
            raise ArithmeticError(f"matrix norm or missing residue check failed for {s}")
        if bool(f.is_irreducible()) != (s in EXCEPTION_DEGREES):
            raise ArithmeticError(f"irreducibility mismatch for {s}")
    if [root_order(polynomial(s)) for s in EXCEPTION_DEGREES] != [7, 21]:
        raise ArithmeticError("wrong orders for the two exceptions")
    print(f"Eliminated {count} residue profiles. Verified {len(supports)} normalized supports, four irreducible.")


def missing_trace_residue(s):
    """Use the power series X f'(X)/f(X) directly, including polynomials with repeated factors."""
    mask = sum(1 << (e-1) for e in s[1:])
    odd_terms = {e for e in s if e % 2}
    seen = set()
    history = 0
    for k in range(1, 7 * s[-1] + 1):
        trace = ((history & mask).bit_count() + (k in odd_terms)) % 2
        history = (history << 1) | trace
        if trace and k % 7 in (1, 6):
            seen.add(k % 7)
            if len(seen) == 2:
                return False
    return True


def direct_check(limit):
    irreducibles = 0
    drops = 0
    seventh = X**7
    sparse_missing = set()
    without_337 = set()
    for n in range(2, limit + 1):
        for size in (1, 3):
            for taps in combinations(range(1, n), size):
                s = (0, *taps, n)
                if s > reciprocal(s):
                    continue
                g = gcd(*s)
                if n <= 25 and g == 1 and missing_trace_residue(s):
                    sparse_missing.add(s)
                f = polynomial(s)
                if not f.is_irreducible():
                    continue
                irreducibles += 1
                degree = EXCEPTION_DEGREES.get(s, n // gcd(7, g))
                y = seventh % f
                if (y.pow_mod(2**degree, f) != y or
                        any(y.pow_mod(2**(degree//p), f) == y for p in prime_divisors(degree))):
                    raise ArithmeticError(f"incorrect seventh-power degree at {s}")
                drops += degree < n
                if n == 21 and X.pow_mod((2**21 - 1)//337, f) == 1:
                    without_337.add(s)
    if sparse_missing != {s for s in TRACE_SUPPORTS if s[-1] <= limit}:
        raise ArithmeticError("the independent power-series enumeration differs")
    if limit >= 21 and without_337 != {(0, 7, 21)}:
        raise ArithmeticError("incorrect list of degree-21 exceptions to divisibility by 337")
    print(f"Checked all normalized power series through degree {min(limit, 25)} and all "
          f"{irreducibles} irreducible reciprocal classes through degree {limit}. "
          f"The seventh power has smaller degree in {drops} classes.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', required=True, help='compiled power_orbit_collisions.cpp')
    parser.add_argument('--through', type=int, default=64, help='degree for independent field computations')
    args = parser.parse_args()
    if args.through < 2:
        parser.error('use a degree of at least two')
    trace_profiles(args.solver)
    direct_check(args.through)
