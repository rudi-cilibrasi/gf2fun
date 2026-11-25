"""Exclude products from the two proper subfields in sparse semiprime degrees."""

import argparse
import json
from functools import cache
from math import gcd
from pathlib import Path

from flint import fmpz, nmod_poly


@cache
def contains_binary_plane(h):
    """A multiplicative subgroup of order h contains a,b,a+b iff it contains x,1+x."""
    x = nmod_poly([0, 1], 2)
    return (x**h+1).gcd((x+1)**h+1).degree() > 0


@cache
def small_orders(p, limit):
    """All nonidentity orders at most limit in the field of prime degree p."""
    return tuple(h for h in range(2*p+1, limit+1, 2*p) if pow(2, p, h) == 1)


def possible_plane_orders(p, q):
    n = p*q
    other_orders = small_orders(q, 2*n)
    possible = []
    for h in small_orders(p, n):
        if not contains_binary_plane(h):
            continue
        if 2*h > n:
            # Two pairs each a single period apart must start at equal powers in the other field.
            if not any(k <= n-h for k in other_orders):
                continue
        elif 3*h > n:
            # With the other order above 2(n-h), the two distinct gaps force a cube root of unity.
            if not any(k <= 2*(n-h) for k in other_orders):
                continue
        possible.append(h)
    return possible


def check_degree(p, q):
    if not 2 < p < q or not (fmpz(p).is_prime() and fmpz(q).is_prime()):
        raise ValueError("expected two distinct odd primes in increasing order")
    return not (possible_plane_orders(p, q) or possible_plane_orders(q, p))


def verify_1243():
    if small_orders(11, 1243) != (23, 89) or small_orders(113, 1243):
        raise ArithmeticError("unexpected proper-subfield orders through 1243")
    if any(contains_binary_plane(h) for h in (23, 89)) or not check_degree(11, 113):
        raise ArithmeticError("the binary plane exclusion failed in degree 1243")
    proper = (2**11-1)*(2**113-1)
    group = 2**1243-1
    if group % proper or gcd(group//proper, proper) != 1:
        raise ArithmeticError("the cofactor overlaps a smaller-degree factor")
    print("Degree 1243. Every irreducible binary polynomial of weight at most five has a root-order "
          "prime of multiplicative degree 1243. The polynomial gcds for 23 and 89 both equal one.")


def verify_1243_bound(threads):
    from flint import ctx
    from check_1229_wheel import verify_chunks
    ctx.threads = threads
    proper = (2**11-1)*(2**113-1)
    cofactor = (2**1243-1)//proper
    path = Path(__file__).resolve().parents[1] / "data" / "degree-1243-wheel-products.json"
    bound = verify_chunks(json.loads(path.read_text()), cofactor=cofactor, step=2486, wheel=5460,
                          seed_degree=1152, start=0, doublings=11, end_bound=262340983306321921)
    print(f"The forced prime exceeds {bound}. The root order of the published product candidate "
          f"exceeds 2^{(proper*bound).bit_length()-1} using its known-factor certificate.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, help="scan odd products of two distinct primes through this degree")
    parser.add_argument("--bound-1243", action="store_true", help="replay the four sieved divisor products")
    parser.add_argument("--threads", type=int, default=1, help="FLINT threads for the divisor products")
    args = parser.parse_args()
    if args.threads < 1:
        parser.error("expected a positive number of threads")
    verify_1243()
    if args.bound_1243:
        verify_1243_bound(args.threads)
    if args.through is not None:
        if args.through < 15:
            parser.error("the first degree with two distinct odd prime factors is 15")
        primes = [p for p in range(3, args.through//3+1, 2) if fmpz(p).is_prime()]
        degrees = sorted((p*q, p, q) for i, p in enumerate(primes) for q in primes[i+1:] if p*q <= args.through)
        excluded = [(n,p,q) for n,p,q in degrees if check_degree(p,q)]
        full_prime = [n for n,p,q in excluded if pow(2,p,q) != 1]
        print(f"Forced a full-degree prime power in {len(excluded)} of {len(degrees)} degrees. "
              f"The component can be taken prime in {len(full_prime)} of them.")
        print("Degrees with a forced prime power:", " ".join(str(n) for n,_,_ in excluded))
