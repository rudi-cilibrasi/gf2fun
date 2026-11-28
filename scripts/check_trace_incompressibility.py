"""Check exceptional trace records and the code lengths for degree-1229 sparse supports."""

import csv
import gzip
import json
from collections import Counter
from fractions import Fraction
from math import comb, gcd

from check_1229_wheel import CONTINUATION, EXTENDED_BOUND, STEP, interval_length
from check_degree_1229 import COFACTOR, GROUP, N, PRIMES
from check_factor_base import DATA, modulus, polynomial


def check_bound(bits, small, deviation, loss, max_exception, min_polynomials):
    q = 2**N
    if (EXTENDED_BOUND + 1)**16 <= COFACTOR:
        raise ArithmeticError("the fifteen-prime bound does not follow from the divisor floor")
    small_loss = Fraction(bits + 2, q) + 3*sum(Fraction(1, p) for p in PRIMES[:small])
    tail_loss = 3*sum((Fraction(1, p) for p in PRIMES[small:]), Fraction(15, EXTENDED_BOUND + 1))
    variance = Fraction((1 + 3*small)**2 * (2*bits + 1)**2, 2**(N-bits))
    exceptional = variance/deviation**2 + tail_loss/loss
    polynomials = (1 - small_loss - deviation - loss) * 2**(N-bits) / N
    if exceptional >= max_exception or polynomials <= min_polynomials:
        raise ArithmeticError(f"failed exceptional fraction or multiplicity at {bits} bits")
    print(f"{bits} trace bits: exceptional fraction < {max_exception}, "
          f"each remaining record has > {min_polynomials} polynomials.")


def check_histogram():
    # Powers of X modulo the primitive degree-ten polynomial with mask 46f.
    n, order = 10, 1023
    powers = [1]
    for _ in range(order - 1):
        value = powers[-1] << 1
        powers.append(value ^ 0x46f if value >> n else value)
    if len(set(powers)) != order or set(powers) != set(range(1, order+1)):
        raise ArithmeticError("incomplete field logarithm table")
    logs = {value: i for i, value in enumerate(powers)}
    traces = []
    for i in range(order):
        value = 0
        for j in range(n):
            value ^= powers[(i << j) % order]
        if value not in (0, 1):
            raise ArithmeticError("absolute trace outside the binary field")
        traces.append(value)

    # Four odd moments each at infinity and zero. Sieve the prime 3 first.
    indices = (1, 3, 5, 7, -1, -3, -5, -7)
    size = 1 << len(indices)
    weighted, removed, good = ([0]*size for _ in range(3))
    for i in range(1, order):
        j = logs[powers[i] ^ 1]
        exponents = (i, j, i-j)
        record = sum(traces[k*i % order] << b for b, k in enumerate(indices))
        weighted[record] += 1 - sum(t % 3 == 0 for t in exponents)
        removed[record] += any(gcd(t, 11*31) != 1 for t in exponents)
        good[record] += all(gcd(t, order) == 1 for t in exponents)
    if any(w-r > v or v % n for w, r, v in zip(weighted, removed, good)):
        raise ArithmeticError("the sieve lower bound or Frobenius orbit count failed")

    transform = [sum((-1 if (s & a).bit_count() % 2 else 1)*v
                     for a, v in enumerate(weighted)) for s in range(size)]
    if sum(c*c for c in transform[1:]) != size*sum(v*v for v in weighted) - sum(weighted)**2:
        raise ArithmeticError("incorrect centered Parseval identity")
    if max(c*c for c in transform[1:]) > (4*(2*len(indices)+1))**2 * 2**n:
        raise ArithmeticError("nonzero Fourier coefficient exceeds the character bound")
    print(f"Degree {n}: {sum(v > 0 for v in good)} of {size} records contain "
          f"the {sum(good)//n} polynomials with all six images primitive.")


def check_sparse_failure_codes():
    with gzip.open(DATA / "degree-1229-irreducible-supports.csv.gz", "rt", newline="") as source:
        counts = Counter()
        failures = []
        for row in csv.DictReader(source):
            mask = int(row["missing_mask"])
            counts[mask] += 1
            if mask:
                failures.append(tuple(int(row[key]) for key in ("a", "b", "c", "missing_mask")))
    with (DATA / "degree-1229-order-exceptions.csv").open(newline="") as source:
        archive = [tuple(map(int, row)) for row in list(csv.reader(source))[1:]]
    if counts != {0: 319572, 1: 5, 2: 6} or sorted(failures) != sorted(archive):
        raise ArithmeticError("the known failure list disagrees with the sparse census")
    x = polynomial(2)
    for a, b, c, mask in failures:
        f = modulus(N, (a, b, c))
        observed = sum(1 << i for i, prime in enumerate(PRIMES) if x.pow_mod(GROUP//prime, f) == 1)
        if mask != observed:
            raise ArithmeticError(f"incorrect order mask for taps {(a, b, c)}")

    # The ranks below concern reciprocal pairs. The unknown classes have no size bound yet.
    survivors = counts[0]
    if (len(failures)-1).bit_length() != 4 or (survivors-1).bit_length() != 19:
        raise ArithmeticError("incorrect fixed-length ranks in the observed census")
    record = json.loads(CONTINUATION.read_text())
    panels = record["panels"]
    bound = EXTENDED_BOUND + len(panels)*STEP*interval_length(12)
    if (bound != record["end_bound"] or (bound+1)**15 <= COFACTOR or
            any(gcd(panel["combined"], COFACTOR) != 1 for panel in panels)):
        raise ArithmeticError("the archived wheel products do not give the fourteen-prime bound")
    prime_limit = 14
    fourteen_bit_bound = survivors - prime_limit*2**14
    threshold = (survivors+prime_limit-1)//prime_limit
    mixed_bound = survivors - 5*2**15 - (prime_limit-5)*2**14
    if fourteen_bit_bound != 90196 or threshold != 22827 or mixed_bound != 8276:
        raise ArithmeticError("incorrect conditional count for the remaining primes")
    print("The eleven known failing reciprocal pairs have a 4-bit rank. "
          f"A 14-bit rank per remaining prime would force at least {fourteen_bit_bound} "
          f"primitive reciprocal pairs. With five 15-bit ranks and nine 14-bit ranks, "
          f"at least {mixed_bound} pairs would be primitive. A counterexample needs a "
          f"class of at least {threshold}.")


if __name__ == "__main__":
    check_bound(1200, 0, Fraction(2, 3), Fraction(1, 12), Fraction(3, 100), 100_000)
    check_bound(1180, 2, Fraction(5, 8), Fraction(1, 16), Fraction(1, 2**19), 2**37)
    if (comb(N-1, 3)-1).bit_length() != 29:
        raise ArithmeticError("incorrect fixed-length pentanomial support code")
    check_histogram()
    check_sparse_failure_codes()
