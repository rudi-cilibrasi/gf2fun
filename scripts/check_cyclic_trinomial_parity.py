"""Check the discriminant formula with two odd exponents and even exponents divisible by eight."""

import argparse
import csv
from collections import Counter
from itertools import combinations, product
from math import isqrt
from pathlib import Path

from flint import fmpz_poly, nmod_poly


def inverse_mod(value, modulus):
    """Extended Euclidean algorithm on binary polynomial masks."""
    r, s = modulus, value
    a, b = 0, 1
    while s:
        if r.bit_length() < s.bit_length():
            r, s, a, b = s, r, b, a
        shift = r.bit_length() - s.bit_length()
        r ^= s << shift
        a ^= b << shift
        if r == 0:
            return b if s == 1 else None
    return None


def discriminant_mod_eight(even, u, v):
    g = (v - u) // 2
    if not (0 < u < v and u % 2 and (v - u) % 4 == 2 and 0 in even
            and all(e % 8 == 0 for e in even)):
        raise ValueError("expected constant one, even exponents divisible by eight, and odd half-gap")
    mask = 0
    for e in even:
        mask ^= 1 << ((e // 2) % g)
    inverse = inverse_mod(mask, (1 << g) | 1)
    if inverse is None:
        return None
    n = max(v, max(even))
    target = -u * ((g + 1) // 2) % g
    bit = (inverse >> target) & 1
    return (-1)**(n // 2) * pow(v, n, 8) * (1 + 4 * bit) % 8


def check_lifts(through):
    checked = squarefree = 0
    for n in range(3, through + 1):
        even_taps = range(8, n + 1, 8)
        for u, v in combinations(range(1, n + 1, 2), 2):
            if (v - u) % 4 != 2:
                continue
            for choices in product((False, True), repeat=len(even_taps)):
                even = (0, *(e for e, bit in zip(even_taps, choices) if bit))
                if max(v, max(even)) != n:
                    continue
                support = (*even, u, v)
                coeffs = [int(i in support) for i in range(n + 1)]
                factors = nmod_poly(coeffs, 2).factor()[1]
                disc = discriminant_mod_eight(even, u, v)
                checked += 1
                if any(m != 1 for _, m in factors):
                    if disc is not None:
                        raise ArithmeticError(f"missed a repeated factor at {support}")
                    continue
                squarefree += 1
                if (disc != int(fmpz_poly(coeffs).discriminant()) % 8
                        or (len(factors) - n) % 2 != int(disc == 5)):
                    raise ArithmeticError(f"discriminant or binary factor parity mismatch at {support}")
    print(f"Verified {checked} binary polynomials through degree {through}, "
          f"including integer discriminants for all {squarefree} squarefree lifts.")


def census_1229(irreducible_path):
    """Count every even-tap pair for each odd prime half-gap in degree 1229."""
    n = 1229
    irreducibles = {}
    if irreducible_path:
        with irreducible_path.open(newline="") as stream:
            for row in csv.DictReader(stream):
                a, b, c = (int(row[k]) for k in ("a", "b", "c"))
                missing = int(row["missing_mask"])
                irreducibles[a, b, c] = irreducibles[n-c, n-b, n-a] = missing
        if len(irreducibles) != 639166:
            raise ValueError("expected the complete degree-1229 --list output")
    counts = Counter()
    for g in range(3, n // 2 + 1, 2):
        if any(g % d == 0 for d in range(3, isqrt(g) + 1, 2)):
            continue
        u = n - 2*g
        target = -u * ((g + 1) // 2) % g
        inverses = [inverse_mod(3 ^ (1 << v), (1 << g) | 1) for v in range(g)]
        scalars = [0] + [pow(i, -1, g) for i in range(1, g)]
        for a, c in combinations(range(8, n, 8), 2):
            e, f = (a // 2) % g, (c // 2) % g
            if e:
                scale = scalars[e]
                inverse = inverses[(f * scale) % g]
                bit = None if inverse is None else (inverse >> (target * scale % g)) & 1
            else:
                bit = int((target + f) % g == 0)
            counts["supports"] += 1
            counts["repeated" if bit is None else "odd" if bit else "even"] += 1
            if irreducibles:
                taps = tuple(sorted((u, a, c)))
                if taps in irreducibles:
                    if bit != 1:
                        raise ArithmeticError(f"parity excluded irreducible {taps}")
                    counts["irreducible"] += 1
                    counts["all_five"] += int(irreducibles[taps] == 0)
    print(f'{counts["supports"]:,} supports, {counts["repeated"]:,} with a repeated factor, '
          f'{counts["even"]:,} squarefree with even factor count, {counts["odd"]:,} with odd count.')
    if irreducibles:
        print(f'{counts["irreducible"]:,} irreducibles, {counts["all_five"]:,} pass all five order tests.')


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=48)
    parser.add_argument("--census-1229", action="store_true", help="count parity for odd prime half-gaps")
    parser.add_argument("--irreducibles", type=Path, help="compare the census against complete --list output")
    args = parser.parse_args()
    if args.through < 3:
        parser.error("expected a maximum degree of at least three")
    if args.irreducibles and not args.census_1229:
        parser.error("--irreducibles requires --census-1229")
    if args.census_1229:
        census_1229(args.irreducibles)
    else:
        check_lifts(args.through)
