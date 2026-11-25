"""Split the orders of the small binary fields between two pentanomial exponents."""

import argparse
from collections import defaultdict
from math import isqrt, lcm, prod


def cyclotomic_values(field_orders):
    """Extract Phi_d(2) from 2^d-1 in ascending divisor order."""
    values = field_orders.copy()
    for d in range(1, len(values)):
        for multiple in range(2*d, len(values), d):
            values[multiple] //= values[d]
    return values


def split_orders(cutoff):
    if cutoff < 1:
        raise ValueError("the cutoff must be positive")
    orders = [1] + [(1 << d) - 1 for d in range(1, cutoff+1)]
    cyclotomic = cyclotomic_values(orders)
    period = lcm(*orders)
    if prod(cyclotomic) != period:
        raise ArithmeticError("cyclotomic product and field-order lcm differ")

    best = (period, 2)
    cores = list(range(cutoff+1))
    primes = []
    for prime in range(2, max(2, isqrt(cutoff))+1):
        if any(prime % p == 0 for p in primes if p*p <= prime):
            continue
        primes.append(prime)
        blocks = defaultdict(list)
        for d in range(1, cutoff+1):
            blocks[cores[d]].append(d)
        weighted = [(prod(cyclotomic[d] for d in block if prime*d > cutoff), block)
                    for block in blocks.values()]
        loads = [1, 1]
        periods = [1, 1]
        for weight, block in sorted(weighted, reverse=True):
            side = 0 if loads[0] <= loads[1] else 1
            loads[side] *= weight
            # Every smaller index divides a multiple in the upper half.
            periods[side] = lcm(periods[side], *(orders[d] for d in block if 2*d > cutoff))
        small, large = sorted(periods)
        taps = (large, 2*small)
        if sum(taps) < sum(best):
            best = taps
        for d in range(1, cutoff+1):
            while cores[d] % prime == 0:
                cores[d] //= prime

    u, v = best
    if not (u % 2 and v % 2 == 0 and all(u % m == 0 or v % m == 0 for m in orders)):
        raise ArithmeticError("the exponents do not cover every small field")
    return u, v, period


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cutoff", nargs="+", type=int, help="maximum factor degrees to exclude")
    parser.add_argument("--exponents", action="store_true", help="print the two exponents in hexadecimal")
    args = parser.parse_args()
    for cutoff in args.cutoff:
        if cutoff < 1:
            parser.error("the cutoff must be positive")
        u, v, period = split_orders(cutoff)
        first = u+v+1
        if first.bit_length() <= 60:
            print(f"B={cutoff}: every degree from {first}, taps {u} and {v}.")
        else:
            print(f"B={cutoff}: first degree has {first.bit_length()} bits, "
                  f"one-tap threshold has {(period+3).bit_length()} bits.")
        if args.exponents:
            print(f"u={u:#x}\nv={v:#x}")
