"""Verify the primitive trace count and compare both endpoints of degree-1229 pentanomials."""

import argparse
import csv
import gzip
from fractions import Fraction
from math import comb, isqrt, lcm

from flint import fq_default_ctx

from check_1229_wheel import EXTENDED_BOUND
from check_degree_1229 import COFACTOR, GROUP, N, PRIMES
from check_factor_base import DATA, irreducible, modulus, polynomial


def field_sum(terms, field):
    return sum(terms, field.zero())


def check_local_identity():
    # Include a pole degree dividing the root degree and two coprime degrees.
    for n, d in ((5, 2), (6, 2), (4, 3)):
        extension = lcm(n, d)
        field = fq_default_ctx(p=2, degree=extension, var="t")
        size = 2**extension - 1
        primes = [p for p in range(2, size+1) if size % p == 0
                  and all(p % j for j in range(2, isqrt(p)+1))]
        for mask in range(2, size+1):
            g = field([(mask >> j) & 1 for j in range(extension)])
            if all(g**(size//p) != 1 for p in primes):
                break
        else:
            raise ArithmeticError("no generator in small validation field")
        z = g**(size//(2**n-1))
        beta = g**(size//(2**d-1))
        for j in (1, 3, 5):
            moment = field_sum(((beta - z**(2**i))**(-j) for i in range(n)), field)
            doubled = field_sum(((beta - z**(2**i))**(-2*j) for i in range(n)), field)
            if moment**(2**d) != moment or moment**2 != doubled:
                raise ArithmeticError("incorrect trace field or doubling rule")
            for power in range(d):
                gamma = beta**power
                rational = field_sum((gamma**(2**i)/(z-beta**(2**i))**j for i in range(d)), field)
                left = field_sum(((gamma*moment)**(2**i) for i in range(d)), field)
                right = field_sum((rational**(2**i) for i in range(n)), field)
                if left != right:
                    raise ArithmeticError("binary and closed-point trace pairings disagree")


def check_count():
    g = 598
    if (EXTENDED_BOUND+1)**16 <= COFACTOR:
        raise ArithmeticError("missing bound on the number of cofactor primes")
    density = sum((Fraction(1, p) for p in PRIMES), Fraction(15, EXTENDED_BOUND+1))
    if density >= Fraction(1, 20000):
        raise ArithmeticError("prime reciprocal sum exceeds allowance")
    lower = Fraction((GROUP+1-g-2)*19997, 20000*2**g)
    lower -= 58*(2*g+1)*(isqrt(GROUP+1)+1)
    if lower <= N * 2**618:
        raise ArithmeticError("finite count is too small")
    g = 596
    lower = Fraction((GROUP+1-g-2)*19997, 20000*2**g)
    lower -= 58*(2*g+1)*(isqrt(GROUP+1)+1)
    heavy_patterns = sum(comb(18, j) for j in range(12, 19))
    surviving = lower/N - Fraction(3*2**614*heavy_patterns, 310)
    if surviving <= 2**619:
        raise ArithmeticError("twelve-term bound is too small")


def parts(taps):
    even = (0, *(j//2 for j in taps if j % 2 == 0))
    odd = (*(j//2 for j in taps if j % 2), N//2)
    return even, odd


def polynomial_mask(terms):
    return sum(1 << j for j in terms)


def cross_product(even, odd, a, b):
    value = 0
    for j in even:
        value ^= b << j
    for j in odd:
        value ^= a << j
    return value


LOW_MASKS = [(k, (1 << k)-1) for k in (1024, 512, 256, 128, 64, 32, 16, 8, 4, 2, 1)]
LUCAS_MASKS = [sum(1 << i for i in range(N) if i & j == j) for j in range(5)]


def valuation_one(value):
    """Read the first Taylor bit at one, folding in characteristic two for larger valuations."""
    for j, mask in enumerate(LUCAS_MASKS):
        if (value & mask).bit_count() % 2:
            return j
    result = 0
    for half, mask in LOW_MASKS:
        high = value >> half
        folded = (value & mask) ^ high
        if folded:
            value = folded
        else:
            value = high
            result += half
    return result


def check_examples():
    failing, passing = (162, 170, 604), (136, 138, 604)
    e, o = parts(failing)
    e2, o2 = parts(passing)
    w = cross_product(e, o, polynomial_mask(e2), polynomial_mask(o2))
    if w != polynomial_mask((682, 683, 695, 699)):
        raise ArithmeticError("incorrect sparse determinant")
    for taps, expected in ((failing, [PRIMES[0]]), (passing, [])):
        f = modulus(N, taps)
        x = polynomial(2)
        if not irreducible(f) or [p for p in PRIMES if x.pow_mod(GROUP//p, f) == 1] != expected:
            raise ArithmeticError("incorrect order comparison")


def compare_census():
    failures, passed = [], []
    with gzip.open(DATA / "degree-1229-irreducible-supports.csv.gz", "rt", newline="") as source:
        for row in csv.DictReader(source):
            support = tuple(int(row[key]) for key in ("a", "b", "c"))
            for taps in (support, tuple(N-k for k in reversed(support))):
                if int(row["missing_mask"]):
                    failures.append((taps, *parts(taps)))
                else:
                    passed.append(taps)
    if len(failures) != 22 or len(passed) != 639144:
        raise ArithmeticError("incomplete support census")
    maxima = [-1]*5
    examples = [None]*5
    for taps in passed:
        a, b = (polynomial_mask(v) for v in parts(taps))
        for failed, even, odd in failures:
            w = cross_product(even, odd, a, b)
            if not w:
                raise ArithmeticError("two distinct irreducibles have zero determinant")
            zero = (w & -w).bit_length()-1
            infinity = N-w.bit_length()
            one = valuation_one(w)
            values = (zero, min(zero, infinity), zero+infinity,
                      min(zero, one, infinity), zero+one+infinity)
            for index, value in enumerate(values):
                if value > maxima[index]:
                    maxima[index] = value
                    examples[index] = (failed, taps, (zero, one, infinity))
    for name, maximum, example in zip(("zero", "balanced ends", "sum of ends", "balanced three", "sum of three"), maxima, examples):
        print(name, maximum, example, flush=True)
    if maxima != [862, 574, 1211, 129, 1212]:
        raise ArithmeticError(f"unexpected trace agreement maxima {maxima}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", action="store_true", help="compare all failed and surviving sparse supports")
    args = parser.parse_args()
    check_local_identity()
    check_count()
    check_examples()
    print("Every 598-bit assignment has more than 2^618 representatives with all six images primitive.")
    print("More than 2^619 have all six images primitive and at most twelve odd terms.", flush=True)
    if args.census:
        compare_census()
