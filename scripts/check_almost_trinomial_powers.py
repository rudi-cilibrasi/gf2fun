"""Bound weights of powers and binary homographies of almost primitive trinomial roots."""

import argparse
import csv
import heapq
from functools import cache
from math import comb, gcd, isqrt
from pathlib import Path

import numpy as np


TABLE = Path(__file__).resolve().parents[1] / "data/almost-trinomial-power-windows.csv"
WIDTH = 64


def x_power(n, modulus):
    """X^n modulo a small binary polynomial, for checking the cofactor."""
    value = 1
    for _ in range(n):
        value <<= 1
        if value.bit_length() == modulus.bit_length():
            value ^= modulus
    return value


@cache
def binary_period(modulus):
    value = 1
    for k in range(1, 1 << (modulus.bit_length() - 1)):
        value <<= 1
        if value.bit_length() == modulus.bit_length():
            value ^= modulus
        if value == 1:
            return k
    raise ValueError("the cofactor has noninvertible constant term")


def offsets(mask):
    return [j for j in range(1, mask.bit_length()) if mask & (1 << j)]


def traces(limit, lags):
    """Coefficients of -Z P'/P modulo 64 for P = 1 + sum Z^lag."""
    result = np.zeros(limit + 1, dtype=np.uint8)
    for j in lags:
        if j <= limit:
            result[j] = -j % WIDTH
    # At most min(lags) successive outputs depend only on previous blocks.
    block = min(lags)
    for start in range(1, limit + 1, block):
        end = min(start + block, limit + 1)
        for lag in lags:
            first = max(start, lag)
            if first < end:
                result[first:end] -= result[first-lag:end-lag]
    return result


def quotient_traces(limit, trim_lags, cofactor):
    result = traces(limit, trim_lags)
    # X^L = 1 mod 2 in the cofactor algebra implies X^(32L) = 1 mod 64.
    period = (WIDTH // 2) * binary_period(cofactor)
    short = traces(min(limit, period), offsets(cofactor))
    if limit <= period:
        result -= short
    else:
        # Positive-index traces repeat; index zero in traces() is a sentinel.
        blocks, tail = divmod(limit, period)
        result[1:1+blocks*period].reshape(blocks, period)[:] -= short[1:]
        result[1+blocks*period:] -= short[1:1+tail]
    return result


@cache
def euler_digits():
    mu = [0, 1]
    for j in range(2, WIDTH):
        mu.append(-sum(mu[d] for d in range(1, j) if j % d == 0))
    digits = []
    for j in range(1, WIDTH):
        two_part = j & -j
        odd_part = j // two_part
        terms = [(two_part*d, mu[odd_part//d]) for d in range(1, odd_part+1)
                 if odd_part % d == 0 and mu[odd_part//d]]
        digits.append((j, two_part, pow(odd_part, -1, WIDTH), terms))
    return digits


def coefficients(sums, first, stop):
    """Leading coefficients for the odd powers first, first+2, ..., below stop."""
    count = len(range(first, stop, 2))
    values = np.ones(count, dtype=np.uint64)
    for j, bit, inverse, terms in euler_digits():
        digit = np.zeros(count, dtype=np.uint8)
        for index, sign in terms:
            sample = sums[first*index:stop*index:2*index]
            if sign == 1:
                digit += sample
            else:
                digit -= sample
        select = ((digit * inverse) & bit) != 0
        np.bitwise_xor(values, values << j, out=values, where=select)
    return values


def byte_table(columns):
    table = np.zeros((8, 256), dtype=np.uint64)
    for j, mask in enumerate(columns):
        byte, bit = divmod(j, 8)
        values = np.arange(256) & (1 << bit) != 0
        table[byte, values] ^= np.uint64(mask)
    return table


def translation_table(n):
    return byte_table(sum(1 << h for h in range(j, min(n+1, WIDTH)) if ((h-j) & (n-j)) == h-j)
                      for j in range(min(n+1, WIDTH)))


def translate(values, table):
    result = np.zeros_like(values)
    for byte, column in enumerate(table):
        result ^= column[(values >> (8*byte)) & 255]
    return result


def windows(n, tap, cofactor):
    delta = cofactor.bit_length()-1
    top = n + delta
    if n < 8 or not (0 < tap < top and delta > 0 and cofactor & 1):
        raise ValueError("invalid trinomial or cofactor")
    period = binary_period(cofactor)
    if x_power(top % period, cofactor) ^ x_power(tap % period, cofactor) ^ 1:
        raise ValueError(f"cofactor does not divide the trinomial in degree {n}")
    reverse = int(f"{cofactor:b}"[::-1], 2)
    limit = (WIDTH-1) * n
    high_traces = quotient_traces(limit, [top-tap, top], reverse)
    low_traces = quotient_traces(limit, [tap, top], cofactor)
    for first in range(1, n+1, 32768):
        stop = min(n+1, first+32768)
        yield first, coefficients(high_traces, first, stop), coefficients(low_traces, first, stop)


def summary(n, tap, cofactor, check_small):
    table = translation_table(n)
    folded_lead = byte_table(1 << ((n-j) % WIDTH) for j in range(WIDTH))
    low_translate = byte_table(sum(1 << k for k in range(j+1) if (k & j) == k) for j in range(WIDTH))
    # Remove repeated positions when the leading and trailing windows overlap.
    low_mask = (1 << max(0, min(WIDTH, n+1-WIDTH))) - 1
    least = [2*WIDTH+1] * 3
    pending = []
    small_polynomials = set()

    def translated_bound(upper, lower):
        lead = translate(upper, table)
        extra = int(n >= WIDTH)  # The known constant below the leading window.
        # Mod X^64-1, translation only uses the original low 64 coefficients.
        residual = translate(lower, low_translate) ^ translate(lead, folded_lead) ^ extra
        return np.bitwise_count(lead) + extra + np.bitwise_count(residual)

    for first, high, low in windows(n, tap, cofactor):
        bounds = (np.bitwise_count(high) + np.bitwise_count(low & low_mask),
                  translated_bound(high, low), translated_bound(low, high))
        if n < WIDTH:
            exact = high, translate(high, table), translate(low, table)
        for k, counts in enumerate(bounds):
            # A full-degree irreducible has value 1 at 1, hence odd weight.
            counts |= 1
            least[k] = min(least[k], int(counts.min()))
            for index in np.flatnonzero(counts <= 5):
                pending.append((first+2*int(index), k))
                if n < WIDTH:
                    bits = int(exact[k][index])
                    small_polynomials.update((bits, int(f"{bits:0{n+1}b}"[::-1], 2)))
        if check_small and n <= 128:
            cross_check(n, tap, cofactor, first, high, low, table)
    first_count = len(pending)
    if n >= WIDTH and pending:
        pending = refine_translates(n, tap, cofactor, pending)
    return (*least, first_count, len(pending)), pending, small_polynomials


@cache
def binomial_patterns(width):
    """Packed coefficients of (1+Z)^j for 0 <= j < width."""
    patterns = [1]
    for _ in range(1, width):
        previous = patterns[-1]
        patterns.append(previous ^ (previous << 1))
    return patterns


def trinomial_translated_weight(top, lag, m, width, indices):
    """Count a leading window of the translated trinomial power image by integer Newton sums."""
    common = gcd(top, lag)
    a, b = lag//common, top//common
    positions = m*indices
    quotients = positions//common
    # Enumerate nonnegative solutions of i*lag+j*top = m*k.
    j0 = ((quotients % a)*pow(b, -1, a)) % a
    possible = (positions % common == 0) & (j0*b <= quotients)
    sums = {}
    for index in np.flatnonzero(possible):
        j = int(j0[index])
        i = (int(quotients[index])-j*b)//a
        trace = 0
        while i >= 0:
            value = lag*comb(i+j-1, j) if i else 0
            if j:
                value += top*comb(i+j-1, i)
            trace += -value if (i+j) % 2 else value
            i -= b
            j += a
        if trace:
            sums[int(index)+1] = trace

    # Newton's identity k*c_k = -sum_i s_i*c_(k-i). Only sums of nonzero
    # trace indices can contribute, so store the nonzero coefficients sparsely.
    patterns = binomial_patterns(width)
    translated = patterns[top % width]
    coefficients = {0: 1}
    pending = list(sums)
    heapq.heapify(pending)
    seen = set(pending)
    while pending:
        k = heapq.heappop(pending)
        value = -sum(trace*coefficients[k-j] for j, trace in sums.items() if k-j in coefficients)
        coefficient, remainder = divmod(value, k)
        if remainder:
            raise ArithmeticError(f"nonintegral Newton coefficient at power {m}, index {k}")
        if coefficient:
            coefficients[k] = coefficient
            if coefficient % 2:
                translated ^= patterns[(top-k) % width] << k
            for j in sums:
                if k+j < width and k+j not in seen:
                    heapq.heappush(pending, k+j)
                    seen.add(k+j)
    return (translated & ((1 << width)-1)).bit_count()


def refine_translates(n, tap, cofactor, pending):
    # The archived unresolved large powers send every root of the cofactor
    # to one. Its power image after translation is then just a monomial.
    period = binary_period(cofactor)
    if any(k not in (1, 2) or m % period for m, k in pending):
        raise ArithmeticError("the cofactor does not give a monomial for a remaining image")
    top = n + cofactor.bit_length()-1
    for width in (128, 256, 512, 1024, 2048, 4096):
        indices = np.arange(1, width, dtype=np.int64)
        pending = [(m, k) for m, k in pending
                   if trinomial_translated_weight(top, top-tap if k == 1 else tap,
                                                  m, width, indices) <= 5]
        if not pending:
            break
    return pending


def cross_check(n, tap, cofactor, first, high, low, table):
    """Compare both windows and their translates with full binary companion matrices."""
    from power_images import power_characteristic

    top = n+cofactor.bit_length()-1
    remainder = (1 << top) | (1 << tap) | 1
    quotient = 0
    while remainder.bit_length() >= cofactor.bit_length():
        shift = remainder.bit_length()-cofactor.bit_length()
        quotient ^= 1 << shift
        remainder ^= cofactor << shift
    if remainder:
        raise ArithmeticError("failed exact cofactor division")
    support = [j for j in range(n+1) if quotient & (1 << j)]
    high_translated, low_translated = translate(high, table), translate(low, table)

    def upper_bits(exponents):
        return sum(1 << (n-i) for i in exponents if n-i < WIDTH)

    def translated(exponents):
        result = 0
        for i in exponents:
            # Horner is unnecessary here; (1+X)^i has precisely the submasks of i.
            j = i
            while True:
                if n-j < WIDTH:
                    result ^= 1 << (n-j)
                if not j:
                    break
                j = (j-1) & i
        return result

    for i in range(len(high)):
        m = first+2*i
        exponents = power_characteristic(support, m)
        reciprocal = [n-j for j in exponents]
        expected = (upper_bits(exponents), upper_bits(reciprocal),
                    translated(exponents), translated(reciprocal))
        actual = tuple(int(v[i]) for v in (high, low, high_translated, low_translated))
        if actual != expected:
            raise ArithmeticError(f"companion-matrix mismatch in degree {n}, tap {tap}, power {m}")
        if m in (1, 3, n if n % 2 else n-1):
            # Check the independent, wide-window Newton calculation against a
            # full companion matrix of the unquotiented trinomial in both directions.
            for lag in (top-tap, tap):
                trinomial = power_characteristic((0, top-lag, top), m)
                window = 0
                for j in trinomial:
                    for k in range(max(0, top-WIDTH+1), j+1):
                        if (k & j) == k:
                            window ^= 1 << (top-k)
                count = trinomial_translated_weight(top, lag, m, WIDTH, np.arange(1, WIDTH))
                if count != window.bit_count():
                    raise ArithmeticError(f"sparse Newton mismatch in degree {n}, power {m}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="check every archived source in one degree")
    parser.add_argument("--cross-check-small", action="store_true",
                        help="also check all powers with full companion matrices in degrees through 128")
    args = parser.parse_args()
    with TABLE.open() as source:
        selected = [row for row in csv.DictReader(source)
                    if args.degree is None or int(row["degree"]) == args.degree]
    if not selected:
        parser.error("degree absent from the table")
    small_images = {}
    for row in selected:
        n, tap, cofactor, *expected = map(int, row.values())
        actual, pending, images = summary(n, tap, cofactor, args.cross_check_small)
        if tuple(expected) != actual:
            raise ArithmeticError(f"mismatched bounds in degree {n}, tap {tap}: {actual}")
        if pending and n >= WIDTH:
            raise ArithmeticError("the available windows did not settle all large-degree cases")
        print(f"Degree {n}, tap {tap}, leading bounds {actual[:3]}, {actual[3]} first-pass candidates, "
              f"{len(pending)} pairs of weight at most five.", flush=True)
        if images:
            small_images.setdefault(n, set()).update(images)
    for n, images in small_images.items():
        order = 2**n-1
        # Only the degree-8 and degree-13 sources yield positive rows.
        primes = [p for p in range(2, order+1) if order % p == 0
                  and all(p % d for d in range(2, isqrt(p)+1))]
        primitive = sum(all(x_power(order//p, f) != 1 for p in primes) for f in images)
        print(f"Degree {n}: {len(images)} distinct five-term polynomials including reciprocals, "
              f"{primitive} primitive.")
