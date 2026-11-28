"""Classify equal or reciprocal third, fifth and seventh power images of sparse binary polynomials.

Compile scripts/power_orbit_collisions.cpp with a C++17 compiler and pass it with --solver.
The input polynomial itself is included as the first power image.
"""

import argparse
import csv
import subprocess
import tempfile
from collections import Counter
from itertools import combinations, combinations_with_replacement
from math import gcd, lcm
from pathlib import Path

from flint import fmpz

from check_cubed_parity import X, polynomial, reciprocal
from power_images import norm_pattern, power_characteristic


DATA = Path(__file__).resolve().parents[1] / "data" / "sparse-power-orbit-exceptions.csv"
PAIRS = tuple(combinations((1, 3, 5, 7), 2))


def profiles(modulus, weight):
    """Fix the least exponent at zero, distinguishing the greatest from the interior ones."""
    units = [u for u in range(1, modulus) if gcd(u, modulus) == 1]
    seen = set()
    for end in range(modulus):
        for middle in combinations_with_replacement(range(modulus), weight - 2):
            if (end, middle) in seen or gcd(modulus, end, *middle) != 1:
                continue
            for u in units:
                tip = u * end % modulus
                seen.add((tip, tuple(sorted(u * e % modulus for e in middle))))
                seen.add((tip, tuple(sorted((tip - u * e) % modulus for e in middle))))
            yield (0, *middle, end)


def product_labels(labels, power, modulus, sign):
    if power == 1:
        pattern = (tuple(int(i == j) for i in range(len(labels))) for j in range(len(labels)))
    else:
        pattern = norm_pattern(power, tuple((sign * e) % power for e in labels))
    for counts in pattern:
        point = [sign * (modulus // power) * count for count in counts[1:]]
        if sign == -1:
            point[-1] += modulus
        yield tuple(point)


def matching_supports(source, backend):
    source.seek(0)
    completed = subprocess.run([backend], stdin=source, text=True, stdout=subprocess.PIPE, check=True)
    signed = set()
    for line in completed.stdout.splitlines():
        sign, *exponents = map(int, line.split())
        support = tuple(exponents)
        if (sign not in (1, -1) or len(support) not in (3, 5) or support[0] != 0
                or tuple(sorted(set(support))) != support or gcd(*support) != 1):
            raise ArithmeticError(f"invalid support from the elimination: {line}")
        signed.add((sign, support))
    if any((sign, reciprocal(s)) not in signed for sign, s in signed):
        raise ArithmeticError("a reciprocal is missing from the list")
    return signed


def solve(a, b, backend):
    modulus = lcm(a, b)
    count = 0
    with tempfile.TemporaryFile(mode="w+") as source:
        for weight in (3, 5):
            for labels in profiles(modulus, weight):
                left = tuple(product_labels(labels, a, modulus, 1))
                for sign in (1, -1):
                    terms = Counter(left)
                    terms.update(product_labels(labels, b, modulus, sign))
                    surviving = [p for p, multiplicity in terms.items() if multiplicity % 2]
                    print(weight, modulus, sign, *labels[1:], len(surviving), file=source)
                    for p in surviving:
                        print(*p, file=source)
                    count += 1
        signed = matching_supports(source, backend)
    for sign, support in signed:
        first = power_characteristic(support, a) if a > 1 else support
        second = power_characteristic(support, b)
        if first != (second if sign == 1 else reciprocal(second)):
            raise ArithmeticError(f"characteristic-polynomial mismatch for {a}, {b}, {support}")
    return count, signed


def root_order(f):
    order = 2**f.degree() - 1
    for p, _ in fmpz(order).factor():
        p = int(p)
        while order % p == 0 and X.pow_mod(order // p, f) == 1:
            order //= p
    return order


def verify_roots(a, b, signed, expected):
    rows = set()
    for sign, support in signed:
        if support > reciprocal(support):
            continue
        f = polynomial(support)
        if not f.is_irreducible():
            continue
        n = support[-1]
        order = root_order(f)
        j = next((k for k in range(n) if (a - sign * b * 2**k) % order == 0), None)
        if j is None:
            raise ArithmeticError(f"missing congruence for {support}")
        rows.add((a, b, sign, n, support[1:-1], order, j))
    if rows != {row for row in expected if row[:2] == (a, b)}:
        raise ArithmeticError(f"the archived exceptions differ for {(a, b)}")


def direct_through(limit, pairs, expected):
    """Independent full-order calculation on every normalized sparse irreducible in this range."""
    found = set()
    count = 0
    for n in range(2, limit + 1):
        for taps_count in (1, 3):
            for taps in combinations(range(1, n), taps_count):
                support = (0, *taps, n)
                if gcd(*support) != 1 or support > reciprocal(support):
                    continue
                f = polynomial(support)
                if not f.is_irreducible():
                    continue
                count += 1
                order = root_order(f)
                for a, b in pairs:
                    for sign in (-1, 1):
                        j = next((k for k in range(n) if (a - sign * b * 2**k) % order == 0), None)
                        if j is not None:
                            found.add((a, b, sign, n, taps, order, j))
    if found != {row for row in expected if row[:2] in pairs and row[3] <= limit}:
        raise ArithmeticError("the direct sparse irreducible search differs from the elimination")
    print(f"Direct order tests through degree {limit} verified {count} normalized reciprocal classes.")


def read_exceptions():
    with DATA.open() as stream:
        return {(int(row['a']), int(row['b']), int(row['sign']), int(row['degree']),
                 tuple(map(int, row['taps'].split())), int(row['order']), int(row['frobenius_exponent']))
                for row in csv.DictReader(stream)}


def check_dilations(rows, pairs):
    """Check the first prime lifts of each odd-degree family and the mixed lift at order 91."""
    cases = {}
    for a, b, sign, n, taps, order, _ in rows:
        if (a, b) in pairs and (n % 2 or (a, b) == (3, 5)):
            cases.setdefault((n, taps, order), set()).add((a, b, sign))
    count = 0
    for (n, taps, order), relations in cases.items():
        primes = {int(p) for p, _ in fmpz(order).factor()}
        for d in sorted(primes | {order}):
            f = polynomial(tuple(d * e for e in (0, *taps, n)))
            lifted = d * order
            if (not f.is_irreducible() or X.pow_mod(lifted, f) != 1
                    or any(X.pow_mod(lifted // p, f) == 1 for p in primes)):
                raise ArithmeticError(f"incorrect order or irreducibility in degree {n * d}")
            doubling = {pow(2, j, lifted) for j in range(n * d)}
            if len(doubling) != n * d:
                raise ArithmeticError(f"incorrect doubling period modulo {lifted}")
            for a, b, sign in relations:
                if not any((a - sign * b * h) % lifted == 0 for h in doubling):
                    raise ArithmeticError(f"missing relation for {(a, b, sign)} modulo {lifted}")
            count += 1
    print(f"Verified {count} dilations by irreducibility, exact order and signed congruences.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', required=True, help='compiled power_orbit_collisions.cpp')
    parser.add_argument('--pair', nargs=2, type=int, metavar=('A', 'B'), help='one of the six increasing pairs')
    parser.add_argument('--through', type=int, default=24, help='directly check all normalized sparse irreducibles up to this degree')
    args = parser.parse_args()
    pairs = PAIRS if args.pair is None else [tuple(args.pair)]
    if any(pair not in PAIRS for pair in pairs) or args.through < 2:
        parser.error('use two different members of 1, 3, 5, 7 in increasing order and a degree of at least two')
    expected = read_exceptions()
    direct_through(args.through, pairs, expected)
    check_dilations(expected, pairs)
    for a, b in pairs:
        count, signed = solve(a, b, args.solver)
        verify_roots(a, b, signed, expected)
        print(f"Powers {a} and {b}: {count} signed profiles, {len(signed)} normalized signed supports.", flush=True)


if __name__ == '__main__':
    main()
