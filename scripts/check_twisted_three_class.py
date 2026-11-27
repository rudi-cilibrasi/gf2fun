"""Certify two imaginary quadratic class numbers and the full 3-parts of the twisted root orders."""

import argparse
import json
from itertools import compress
from math import ceil, isqrt, prod
from pathlib import Path

from flint import arb, arb_series, ctx, fmpz

from check_twisted_conductor import form_power, reduced_form
from check_twisted_ray import eligible


DATA = Path(__file__).resolve().parents[1] / "data" / "translation-lift-orders.json"
PARAMETERS = {141: (21, 82), 191: (26, 108)}  # binary logarithms of the smoothness and sum cutoffs
MESH = 1024
SCALE = 1 << 48


def primes_through(limit):
    """Segmented Eratosthenes sieve over odd integers."""
    yield 2
    root = isqrt(limit)
    small = bytearray([1]) * (root + 1)
    for p in range(2, isqrt(root) + 1):
        if small[p]:
            small[p*p::p] = bytes((root - p*p) // p + 1)
    base = [p for p in range(3, root + 1, 2) if small[p]]
    for lo in range(3, limit + 1, 1 << 20):
        hi = min(lo + (1 << 20), limit + 1)
        block = bytearray([1]) * ((hi - lo + 1) // 2)
        for p in base:
            if p*p >= hi:
                break
            start = max(p*p, ((lo + p - 1) // p) * p)
            if start % 2 == 0:
                start += p
            if start < hi:
                block[(start-lo)//2::p] = bytes((hi-1-start) // (2*p) + 1)
        yield from compress(range(lo, hi, 2), block)


def bin_starts(y_bits):
    # Floating point supplies a guess. Integer powers certify both endpoints.
    result = []
    for j in range(y_bits * MESH + 1):
        threshold = 1 << j
        first = ceil(2 ** (j / MESH))
        while (first - 1)**MESH >= threshold:
            first -= 1
        while first**MESH < threshold:
            first += 1
        result.append(first)
    return result


def log_coefficients(disc, y_bits):
    y = 1 << y_bits
    starts = bin_starts(y_bits)
    coeffs = [0] * len(starts)
    mass = count = j = 0
    for p in primes_through(y):
        symbol = 1 if p == 2 else int(disc.jacobi(p))
        if not symbol:
            continue
        while j + 1 < len(starts) and starts[j + 1] <= p:
            j += 1
        power, r = p, 1
        while power <= y:
            value = SCALE // (r * power)
            coeffs[r*j] += -value if symbol < 0 and r % 2 else value
            mass += value
            count += 1
            power *= p
            r += 1
    return coeffs, mass, count


def smooth_bound(disc, y_bits, x_bits):
    coeffs, mass, count = log_coefficients(disc, y_bits)
    log_error = arb(count) / SCALE + 3 / (arb(1 << y_bits).sqrt() - 1)
    series_error = (arb(mass) / SCALE + log_error).exp() * log_error
    length = MESH * x_bits + 1
    ctx.cap = length
    logarithm = arb_series([arb(t) / SCALE for t in coeffs], prec=length)
    coefficients = logarithm.exp()
    total = maximum = arb(0)
    for i in range(length):
        total += coefficients[i]
        maximum = maximum.max(abs(total))
    # Above 256 the logarithmic bin can include extra integers at the right endpoint.
    bound = maximum + series_error + arb(x_bits) * arb(2).log() / (MESH - 1) + arb(1)/256
    total = arb(0)
    for n in range(1, 256):
        total += arb(int(disc.jacobi(n // (n & -n)))) / n
        bound = bound.max(abs(total))
    return bound


def character_bound(disc, y_bits, x_bits):
    y, x = 1 << y_bits, 1 << x_bits
    # Bound unordered tuples of distinct large primes with product <= x.
    grid = 256
    length = grid * x_bits // y_bits + 1
    bins = [arb(0)] * grid + [(arb(j+1)/j).log() for j in range(grid, length)]
    bins[grid] += 1 / arb(y).log()**2
    ctx.cap = length
    tuples = arb_series(bins, prec=length).exp()
    rough = sum(tuples[j] for j in range(length)) + (1 + arb(x).log()) / (y - 1)
    tail = 2 * arb(-disc).sqrt() * (1 + arb(-disc).log()) / x
    return smooth_bound(disc, y_bits, x_bits) * rough + tail


def check(k, h):
    p = 2**k + 5
    if not eligible(p) or p % 24 != 13 or h % 3 == 0:
        raise ValueError(f"invalid discriminant or order for k={k}")
    disc = fmpz(-3*p)
    prime = reduced_form(disc, 2, 1)
    factors = fmpz(h).factor()
    if (prod(int(q)**e for q, e in factors) != h or not all(q.is_prime() for q, _ in factors)
            or form_power(disc, prime, h)[0] != 1
            or any(form_power(disc, prime, h // int(q))[0] == 1 for q, _ in factors)):
        raise ValueError(f"incorrect order of the prime above two for k={k}")
    limit = character_bound(disc, *PARAMETERS[k])
    threshold = 3 * arb.pi() * h / arb(-disc).sqrt()
    if not limit < threshold:
        raise ArithmeticError(f"class number upper bound inconclusive for k={k}")
    lifted_disc = 9*disc
    lifted = form_power(lifted_disc, reduced_form(lifted_disc, 2, 1), h)
    if lifted != (9, 3, (3*p+1) // 4):
        raise ArithmeticError(f"unexpected conductor-three form for k={k}")
    n = p - 1
    power = 3
    while n % 3 == 0:
        n //= 3
        power *= 3
    print(f"k={k}: L(1,chi) <= {limit}, below 3*pi*H/sqrt(|D|) = {threshold}.")
    print(f"The class number is {h}. The exact 3-part of the root order is {power}.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exponent", choices=PARAMETERS, type=int, help="check one exponent")
    args = parser.parse_args()
    ctx.prec = 150
    orders = json.loads(DATA.read_text())["imaginary_quadratic_principalization"]
    for k in ([args.exponent] if args.exponent else PARAMETERS):
        check(k, orders[str(k)])
