"""Check degree-1229 collisions between products of conjugates of a nonprimitive root."""

import argparse
import json
from fractions import Fraction
from math import gcd, isqrt

from flint import fmpz, fmpz_mod_poly_ctx

from check_degree_1229 import COFACTOR, N
from check_factor_base import DATA


LEAST = 8317007399072301058
FREQUENCIES = DATA / "degree-1229-signed-frequency-product.json"
TWELVE_U = (0, 0, 0, 0, -6, -6, -6, -6, -2, -2, -2, -2,
            -2, -2, -14, -14, 0, 0, 0, 0, 0, 0, 0, 0)


def root_product_polynomial(points, modulus):
    """Build a monic polynomial with the supplied roots by balanced multiplications."""
    ring = fmpz_mod_poly_ctx(modulus)
    layer = [ring([-x, 1]) for x in points]
    while len(layer) > 1:
        pairs = [layer[i]*layer[i+1] for i in range(0, len(layer)-1, 2)]
        if len(layer) % 2:
            pairs.append(layer[-1])
        layer = pairs
    return layer[0]


def derivative_product(points, modulus):
    polynomial = root_product_polynomial(points, modulus)
    product = fmpz(1)
    for value in polynomial.derivative().multipoint_evaluate(points):
        product = product*int(value) % modulus
    return int(product)


def check_frequencies(replay):
    record = json.loads(FREQUENCIES.read_text())
    bound = record['bound']
    if (record['degree'] != N or bound != 2**20 or bound >= LEAST or
            gcd(record['residue'], COFACTOR) != 1):
        raise ArithmeticError("incorrect signed frequency certificate")
    if replay:
        c = fmpz(COFACTOR)
        points = [pow(fmpz(t), 2*N, c) for t in range(1, bound, 2)]
        if derivative_product(points, c) != record['residue']:
            raise ArithmeticError("the frequency derivative product does not match the archive")
    return bound


def check_step_function():
    # Cell i is [i/24,(i+1)/24). F is the excess of positive digits over
    # negative digits, less twice the number of exchanges reducing positives.
    signed = [int(4 <= k < 8)-int(16 <= k < 20) for k in range(24)]
    f = [v-2*int(k == 19) for k, v in enumerate(signed)]
    h = [12*v + 1 + TWELVE_U[k] - TWELVE_U[2*k % 24] for k, v in enumerate(f)]
    if (TWELVE_U[::2] != TWELVE_U[1::2] or sum(f) != -2 or
            h[12:] != [-v for v in h[:12]] or sum(v*v for v in h) != 1576 or
            max(map(abs, h)) != 21 or sum(abs(v-h[i-1]) for i, v in enumerate(h)) != 84):
        raise ArithmeticError("incorrect step-function variance or variation")


def sqrt_upper(value):
    value = Fraction(value)
    scale = 10**8
    return Fraction(isqrt(value.numerator*scale**2//value.denominator)+1, scale)


def spectral_bound(bound, energy, height, variation):
    """Outward L2 estimate over the nonzero residues of every remaining prime."""
    main = sqrt_upper(N*(energy + 2*height*variation/LEAST))
    tail = N*variation*sqrt_upper(Fraction(1, 36*bound) + Fraction(3, LEAST))
    return sqrt_upper(Fraction(LEAST, LEAST-1)) * (main+tail)


def check_small_cycles():
    # Check the periodic signed digits and both directions of the local exchange.
    for n, prime in ((3, 7), (5, 31), (9, 73), (11, 23), (11, 89), (15, 151)):
        group = 2**n-1
        for j in range(1, prime):
            residues = [(j << i) % prime for i in range(n)]
            digits = [int(prime < 6*r < 2*prime)-int(4*prime < 6*r < 5*prime) for r in residues]
            # The sign read at r_i is the next digit, in descending binary order.
            positions = [(n-2-i) % n for i in range(n)]
            value = sum(v*(1 << k) for v, k in zip(digits, positions))
            if (value-j*(group//prime)) % group:
                raise ArithmeticError("the signed digits give the wrong exponent")
            for majority in (1, -1):
                starts = [i for i in range(n) if digits[i] == -majority and
                          digits[(i+2) % n] == majority]
                count = sum(19*prime < 24*(r if majority == 1 else prime-r) < 20*prime
                            for r in residues)
                if count != len(starts):
                    raise ArithmeticError("incorrect exchange interval")
                take = min(count, max(0, (digits.count(majority)-digits.count(-majority))//2))
                changed = digits.copy()
                for i in starts[:take]:
                    changed[i] = 0
                    changed[(i+1) % n] = changed[(i+2) % n] = -majority
                new = sum(v*(1 << k) for v, k in zip(changed, positions))
                if (new-value) % group or changed.count(majority) != digits.count(majority)-take:
                    raise ArithmeticError("the local exchange changed the exponent or its count")


def check_ranks(bound):
    mean_half_weight = Fraction(N*(LEAST+1), 6*(LEAST-1))
    signed = spectral_bound(bound, Fraction(1, 3), Fraction(1), 4)
    balanced = spectral_bound(bound, Fraction(197, 432), Fraction(7, 4), 7)
    raw_mean = mean_half_weight + signed/2
    balanced_mean = mean_half_weight + Fraction(1, 2) + 3*balanced**2/N
    for mean, rank, minimum in ((raw_mean, 215, 12*10**15),
                                (balanced_mean, 206, 26*10**14)):
        pairs = Fraction(LEAST-1, 2)*(1-mean/(rank+1))
        if pairs <= minimum:
            raise ArithmeticError(f"insufficient collisions at rank {rank}")
        print(f"More than {minimum:,} unordered collisions have both sides of size at most {rank}.")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--frequencies', action='store_true', help='recompute the modular derivative product')
    parser.add_argument('--threads', type=int, default=1, help='FLINT threads for the product')
    args = parser.parse_args()
    if args.threads < 1:
        parser.error('the thread count must be positive')
    from flint import ctx
    ctx.threads = args.threads
    check_step_function()
    check_small_cycles()
    check_ranks(check_frequencies(args.frequencies))
