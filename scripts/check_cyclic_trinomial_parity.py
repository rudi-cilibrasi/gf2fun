"""Check the discriminant formula with two odd exponents and even exponents divisible by eight."""

import argparse
import csv
import json
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from math import gcd, isqrt, lcm, prod
from pathlib import Path

from flint import fmpz, fmpz_poly, nmod_poly


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


def check_primitive_examples():
    data = Path(__file__).resolve().parents[1] / "data"
    orders = {}
    for name in ("mersenne-1207-1228-factors.json", "mersenne-1230-1280-factors.json"):
        orders.update(json.loads((data / name).read_text()))
    x = nmod_poly([0, 1], 2)
    primes = set()
    degrees = set()
    checks = 0
    with (data / "cyclic-parity-primitive.csv").open(newline="") as stream:
        for row in csv.DictReader(stream):
            n, a, b, c, cutoff = (int(row[k]) for k in ("degree", "a", "b", "c", "cutoff"))
            if not 0 < a < b < c < n or n in degrees or cutoff < 1 or n % 8 not in (0, 3, 5):
                raise ValueError(f"invalid example in degree {n}")
            degrees.add(n)
            support = (0, a, b, c, n)
            even = [e for e in support if e % 2 == 0]
            u, v = (e for e in support if e % 2)
            gap = (v - u) // 2
            period = lcm(*(2**d - 1 for d in range(1, cutoff + 1)))
            low, high = even[1:] if n % 2 else (u, even[1])
            partner = u if n % 2 else v
            if (not fmpz(gap).is_prime() or gcd(gap, n * period) != 1
                    or not 12 * low < n < 16 * low or not 3 * high < n < 4 * high
                    or low % period or (high - partner) % period
                    or gcd(*support) != 1
                    or len({i+j for i, j in combinations_with_replacement(support, 2)}) != 15
                    or discriminant_mod_eight(even, u, v) != (1 if n % 2 else 5)):
                raise ArithmeticError(f"family conditions failed at {support}")
            order = 2**n - 1
            if n == 2203:
                # Lucas--Lehmer proves primality of this full group order.
                state = 4
                for _ in range(n - 2):
                    state = (state * state - 2) % order
                if not fmpz(n).is_prime() or state:
                    raise ArithmeticError(f"Lucas--Lehmer check failed in degree {n}")
                factors = [order]
            else:
                factors = orders[str(n)]
                primes.update(factors)
            f = sum((x**e for e in support), nmod_poly([], 2))
            if (prod(factors) != order or x.pow_mod(order, f) != 1
                    or any(x.pow_mod(order // p, f) == 1 for p in set(factors))):
                raise ArithmeticError(f"order check failed at {support}")
            checks += len(set(factors))
    if not degrees or not all(fmpz(p).is_prime() for p in primes):
        raise ArithmeticError("missing examples or composite group-order factor")
    print(f"Verified {len(degrees)} primitive pentanomials and {checks} prime-index powers.")


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
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--census-1229", action="store_true", help="count parity for odd prime half-gaps")
    mode.add_argument("--primitive-examples", action="store_true", help="verify the full orders of the tabulated examples")
    parser.add_argument("--irreducibles", type=Path, help="compare the census against complete --list output")
    args = parser.parse_args()
    if args.through < 3:
        parser.error("expected a maximum degree of at least three")
    if args.irreducibles and not args.census_1229:
        parser.error("--irreducibles requires --census-1229")
    if args.census_1229:
        census_1229(args.irreducibles)
    elif args.primitive_examples:
        check_primitive_examples()
    else:
        check_lifts(args.through)
