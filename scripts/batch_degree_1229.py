"""Exclude possible divisors 2458j+1 of the degree-1229 cofactor in square blocks."""

import argparse
import json
from pathlib import Path
from math import gcd

from flint import fmpz, fmpz_mod_poly_ctx

from check_degree_1229 import COFACTOR, KNOWN, N


def extend_samples(values, last, ring, modulus, method):
    """Evaluate a polynomial at 0,...,last from its first degree+1 consecutive values."""
    degree = len(values) - 1
    factorial = [fmpz(1)]
    for i in range(1, last + 1):
        factorial.append(factorial[-1] * i % modulus)
    inverse = [fmpz(0)] * (last + 1)
    # Failure exposes a common divisor of last! and the modulus.
    inverse[last] = pow(factorial[last], -1, modulus)
    for i in range(last, 0, -1):
        inverse[i-1] = inverse[i] * i % modulus
    if method == "lagrange":
        weights = [v * inverse[j] * inverse[degree-j] % modulus for j, v in enumerate(values)]
        numerator = ring([(-v if (degree-j) % 2 else v) for j, v in enumerate(weights)])
        reciprocals = ring([0] + [factorial[j-1] * inverse[j] % modulus for j in range(1, last+1)])
        sums = numerator.mul_low(reciprocals, last + 1)
        return values + [factorial[j] * inverse[j-degree-1] * int(sums[j]) % modulus
                         for j in range(degree + 1, last + 1)]
    samples = ring([v * inverse[j] % modulus for j, v in enumerate(values)])
    signs = ring([(-v if j % 2 else v) for j, v in enumerate(inverse[:degree+1])])
    differences = samples.mul_low(signs, degree + 1)
    scaled = differences.mul_low(ring(inverse), last + 1)
    return [factorial[j] * int(scaled[j]) % modulus for j in range(last + 1)]


def block_product(modulus, step, log_block, start=0, method="newton"):
    """Compute the product of 1+step*j for start < j <= start + 2^(2*log_block), modulo modulus."""
    ring = fmpz_mod_poly_ctx(modulus)
    modulus = fmpz(modulus)
    d = 1
    values = [fmpz(1 + step*(start+1)), fmpz(1 + step*(start+2))]
    for _ in range(log_block):
        # If F_d(i) is the product for block i, F_(2d)(i) = F_d(2i) F_d(2i+1).
        extended = extend_samples(values, 4*d + 1, ring, modulus, method)
        d *= 2
        values = [extended[2*i] * extended[2*i+1] % modulus for i in range(d + 1)]
    product = fmpz(1)
    for i in range(d):
        product = product * values[i] % modulus
    return int(product)


def run(log_block, start=0, method="newton", expected=None):
    step = 2 * N
    if gcd(step, COFACTOR) != 1:
        raise ArithmeticError("the progression step shares a cofactor divisor")
    residue = block_product(COFACTOR, step, log_block, start, method)
    if expected is not None and residue != expected:
        raise ArithmeticError("the recomputed progression product differs from the published residue")
    divisor = gcd(residue, COFACTOR)
    bound = 1 + step * (start + (1 << (2*log_block)))
    print(f"Progression from {1+step*(start+1)} through {bound}. Product modulo the cofactor: {residue}.")
    if divisor != 1:
        raise ValueError(f"product gcd {divisor}; subdivide the interval to isolate its factors")
    if start == 0:
        bits = (KNOWN * bound).bit_length() - 1
        print(f"Product gcd 1. Every cofactor prime exceeds {bound}. Root order exceeds 2^{bits}.")
    else:
        print("Product gcd 1. The cofactor is coprime to every progression term in this interval.")
    return bound


PUBLISHED_BOUND = 1 + 2*N*(1 << 45)


def verify_published():
    path = Path(__file__).resolve().parents[1] / "data" / "degree-1229-progression-products.json"
    rows = json.loads(path.read_text())
    if len(rows) != 2:
        raise ValueError("expected two published blocks")
    start = 0
    for row, method in zip(rows, ("newton", "lagrange"), strict=True):
        if row["start"] != start or row["log_block"] != 22:
            raise ValueError("the published blocks have a gap or the wrong length")
        bound = run(22, start, method, row["residue"])
        start += 1 << 44
    if bound != PUBLISHED_BOUND:
        raise ArithmeticError("incomplete interval")
    print(f"Every cofactor prime exceeds {bound}. Root order exceeds 2^{(KNOWN*bound).bit_length()-1}.")
    return bound


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-block", type=int, default=18, help="test 2^(2k) progression terms")
    parser.add_argument("--start", type=int, default=0, help="number of initial progression terms to skip")
    parser.add_argument("--method", choices=("newton", "lagrange"), default="newton")
    parser.add_argument("--published", action="store_true", help="recheck both published blocks")
    args = parser.parse_args()
    if min(args.log_block, args.start) < 0:
        parser.error("expected a nonnegative block exponent and starting index")
    if args.published:
        verify_published()
    else:
        run(args.log_block, args.start, args.method)
