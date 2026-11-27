"""Choose the constant field, curve order and target count for the uniform elliptic order criterion."""

import argparse
from math import isqrt, lcm


def quadratic_bound(n, q, cosets, index_floor):
    """Strict two-moment point inequality after optimizing the middle weight."""
    den = n*index_floor
    gap = cosets*den - (q+1)
    return gap > 0 and 2*gap**2 > den*(q*den + q*q + 1)


def target_count(n, q, index_floor):
    den = n*index_floor
    gap = isqrt(den*(q*den + q*q + 1)//2) + 1
    return (q+1 + gap + den-1)//den


def parameters(n, level):
    if n < 64 or level < 2:
        raise ValueError("expected degree at least 64 and level at least two")
    denom = 2*level-1
    lower = (level*n*n + denom-1)//denom + 4*n
    q = 1 << (lower-1).bit_length()
    step = lcm(2, n)
    order = ((q+1 + step//2)//step)*step
    floor = level*n
    k = target_count(n, q, floor)
    if (not (order-q-1)**2 < 4*q or not k <= order//n <= floor
            or not quadratic_bound(n, q, k, floor) or quadratic_bound(n, q, k-1, floor)
            or (k-7)**2 * denom**2 >= n*n*level*(2*level+1)):
        raise ArithmeticError("uniform elliptic parameter bounds failed")
    return q, order, k


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", type=int)
    parser.add_argument("--level", type=int, default=2)
    args = parser.parse_args()
    if args.degree < 64 or args.level < 2:
        parser.error("expected degree at least 64 and level at least two")
    q, order, k = parameters(args.degree, args.level)
    print(f"Constant field size {q}, cyclic curve order {order}, {k} subgroup targets.")
    print(f"Test prime divisors of 2^{args.degree}-1 up to {args.level*args.degree} or dividing {q-1}.")
