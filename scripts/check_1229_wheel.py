"""Check sieved products for prime divisors of the degree-1229 cofactor."""

import argparse
import json
from math import gcd
from pathlib import Path

from flint import fmpz, fmpz_mod_poly_ctx

from batch_degree_1229 import PUBLISHED_BOUND, extend_samples
from check_degree_1229 import COFACTOR, KNOWN, N


WHEEL = 4*3*5*7*11
STEP = 2*N
SEED_DEGREE = 960
EXTENDED_BOUND = 818085338814611457
DATA = Path(__file__).resolve().parents[1] / "data" / "degree-1229-wheel-products.json"


def wheel_offsets(start):
    # Every cofactor prime is 1 mod 2n, is ±1 mod 8 and exceeds 11.
    return [j for j in range(1, WHEEL+1)
            if (v := 1+STEP*(start+j)) % 8 in (1, 7) and gcd(v, WHEEL//4) == 1]


def interval_length(doublings):
    return WHEEL * SEED_DEGREE * 4**doublings


def wheel_product(start, doublings, method):
    offsets = wheel_offsets(start)
    if len(offsets) != SEED_DEGREE:
        raise ArithmeticError("incorrect number of admissible residues")
    modulus = fmpz(COFACTOR)
    ring = fmpz_mod_poly_ctx(COFACTOR)
    constants = [1+STEP*(start+j) for j in offsets]
    degree = len(constants)
    values = []
    for i in range(degree+1):
        shift = STEP*WHEEL*i
        value = fmpz(1)
        for c in constants:
            value = value*(shift+c) % modulus
        values.append(value)
    for _ in range(doublings):
        extended = extend_samples(values, 4*degree+1, ring, modulus, method)
        degree *= 2
        values = [extended[2*i]*extended[2*i+1] % modulus for i in range(degree+1)]
        del extended
    result = fmpz(1)
    for i in range(degree):
        result = result*values[i] % modulus
    return int(result)


def verify_extension():
    """Replay the four adjacent intervals following the two original products."""
    record = json.loads(DATA.read_text())
    start = (PUBLISHED_BOUND-1)//STEP
    product = 1
    for row in record["chunks"]:
        if row["start"] != start or row["doublings"] != 12:
            raise ValueError("gap or wrong length in the wheel certificate")
        residue = wheel_product(start, row["doublings"], "lagrange")
        if residue != row["residue"]:
            raise ValueError(f"incorrect wheel product after index {start}")
        product = product*residue % COFACTOR
        start += interval_length(row["doublings"])
    bound = 1+STEP*start
    if bound != EXTENDED_BOUND or product != record["combined"] or gcd(product, COFACTOR) != 1:
        raise ValueError("the combined product or the end of the interval failed")
    return bound


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, help="number of progression indices preceding the interval")
    parser.add_argument("--doublings", type=int, default=10, help="number of polynomial doublings")
    parser.add_argument("--method", choices=("newton", "lagrange"), default="newton")
    parser.add_argument("--threads", type=int, default=1, help="FLINT internal thread count")
    args = parser.parse_args()
    if args.threads < 1 or args.doublings < 0 or (args.start is not None and args.start < 0):
        parser.error("expected nonnegative indices and a positive thread count")
    from flint import ctx
    ctx.threads = args.threads
    if args.start is None:
        from batch_degree_1229 import verify_published
        verify_published()
        bound = verify_extension()
        print(f"Every cofactor prime exceeds {bound}. Root order exceeds 2^{(KNOWN*bound).bit_length()-1}.")
    else:
        residue = wheel_product(args.start, args.doublings, args.method)
        end = args.start+interval_length(args.doublings)
        print(f"Indices {args.start+1} through {end}. Residue {residue}. GCD {gcd(residue, COFACTOR)}.")
