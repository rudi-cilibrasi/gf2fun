"""Check sieved products for prime divisors of the degree-1229 cofactor."""

import argparse
import json
from math import gcd
from pathlib import Path

from flint import fmpz, fmpz_mod_poly_ctx

from batch_degree_1229 import PUBLISHED_BOUND, extend_samples
from check_degree_1229 import COFACTOR, KNOWN, N, PRIMES


WHEEL = 4*3*5*7*11
STEP = 2*N
SEED_DEGREE = 960
EXTENDED_BOUND = 818085338814611457
DATA = Path(__file__).resolve().parents[1] / "data" / "degree-1229-wheel-products.json"
CONTINUATION = DATA.with_name("degree-1229-wheel-continuation.json")


def wheel_offsets(start, step=STEP, wheel=WHEEL):
    return [j for j in range(1, wheel+1)
            if (v := 1+step*(start+j)) % 8 in (1, 7) and gcd(v, wheel//4) == 1]


def interval_length(doublings):
    return WHEEL * SEED_DEGREE * 4**doublings


def wheel_product(start, doublings, method, *, cofactor=COFACTOR, step=STEP,
                  wheel=WHEEL, seed_degree=SEED_DEGREE):
    """Product of the retained terms in wheel * seed_degree * 4**doublings indices."""
    offsets = wheel_offsets(start, step, wheel)
    if len(offsets) != seed_degree:
        raise ArithmeticError("incorrect number of admissible residues")
    modulus = fmpz(cofactor)
    ring = fmpz_mod_poly_ctx(cofactor)
    constants = [1+step*(start+j) for j in offsets]
    degree = len(constants)
    values = []
    for i in range(degree+1):
        shift = step*wheel*i
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


def verify_chunks(record, *, cofactor, step, wheel, seed_degree, start, doublings, end_bound):
    """Check the adjacent Lagrange products against the combined Newton residue."""
    product = 1
    for row in record["chunks"]:
        if row["start"] != start or row["doublings"] != doublings:
            raise ValueError("gap or wrong length in the wheel certificate")
        residue = wheel_product(start, doublings, "lagrange", cofactor=cofactor, step=step,
                                wheel=wheel, seed_degree=seed_degree)
        if residue != row["residue"]:
            raise ValueError(f"incorrect wheel product after index {start}")
        product = product*residue % cofactor
        start += wheel*seed_degree*4**doublings
    bound = 1+step*start
    if bound != end_bound or product != record["combined"] or gcd(product, cofactor) != 1:
        raise ValueError("the combined product or the end of the interval failed")
    return bound


def verify_extension():
    """Replay the four intervals following the original degree-1229 products."""
    return verify_chunks(json.loads(DATA.read_text()), cofactor=COFACTOR, step=STEP,
                         wheel=WHEEL, seed_degree=SEED_DEGREE, start=(PUBLISHED_BOUND-1)//STEP,
                         doublings=12, end_bound=EXTENDED_BOUND)


def verify_continuation():
    """Recompute each subsequent Newton product as four independent Lagrange products."""
    record = json.loads(CONTINUATION.read_text())
    start = (EXTENDED_BOUND-1)//STEP
    panels = record["panels"]
    if not panels:
        raise ValueError("empty wheel continuation")
    for panel in panels:
        if len(panel["chunks"]) != 4:
            raise ValueError("a Newton product must span four Lagrange products")
        end = start + interval_length(12)
        verify_chunks(panel, cofactor=COFACTOR, step=STEP, wheel=WHEEL,
                      seed_degree=SEED_DEGREE, start=start, doublings=11, end_bound=1+STEP*end)
        start = end
    bound = 1 + STEP*start
    if bound != record["end_bound"]:
        raise ValueError("incorrect final wheel bound")
    return bound


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--start", type=int, help="number of progression indices preceding the interval")
    action.add_argument("--continuation-only", action="store_true",
                        help="replay the products after the established 818085338814611457 bound")
    parser.add_argument("--doublings", type=int, default=10, help="number of polynomial doublings")
    parser.add_argument("--method", choices=("newton", "lagrange"), default="newton")
    parser.add_argument("--threads", type=int, default=1, help="FLINT internal thread count")
    args = parser.parse_args()
    if args.threads < 1 or args.doublings < 0 or (args.start is not None and args.start < 0):
        parser.error("expected nonnegative indices and a positive thread count")
    from flint import ctx
    ctx.threads = args.threads
    if args.start is None:
        if not args.continuation_only:
            from batch_degree_1229 import verify_published
            verify_published()
            verify_extension()
        bound = verify_continuation()
        all_orders = (KNOWN//PRIMES[1]*bound).bit_length()-1
        passing_orders = (KNOWN*bound).bit_length()-1
        print(f"Every cofactor prime exceeds {bound}. All 639166 irreducible pentanomial "
              f"root orders exceed 2^{all_orders}, and the 639144 passing all four known "
              f"tests have order exceeding 2^{passing_orders}.")
    else:
        residue = wheel_product(args.start, args.doublings, args.method)
        end = args.start+interval_length(args.doublings)
        print(f"Indices {args.start+1} through {end}. Residue {residue}. GCD {gcd(residue, COFACTOR)}.")
