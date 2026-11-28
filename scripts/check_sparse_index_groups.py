"""Check which prime-index subgroups of size at most 300n contain sparse degree-n roots."""

import argparse
from array import array

from flint import fmpz

from check_linear_order_classes import flint_census
from check_sparse_circuit_orders import binary_degree
from check_sparse_root_orders import (cyclotomic_census, excludes_single_tap_prefix, odd_prime_flags,
                                     odd_small_factors, prime_degree_candidates, small_composite_orders)
from check_trinomial_subfield_pairs import prime_divisors


# Number of ones in the full period word for each order left by the gcd sieve.
PERIOD_WEIGHTS = {
    (281, 80929): 143, (1213, 327511): 147, (2591, 766937): 137,
    (3863, 1120271): 133, (5431, 1401199): 137, (6883, 1885943): 153,
    (7129, 1867799): 139, (8731, 2514529): 129, (9137, 2704553): 139,
    (9337, 2614361): 139, (9403, 2576423): 145, (11719, 3093817): 121,
}


def rotate(bits, shift, length):
    shift %= length
    return ((bits << shift) | (bits >> (length-shift))) & ((1 << length)-1)


def unit_trace_word(n, r):
    """Compute one complete binary Gauss-period word using the algebra of doubling orbits."""
    k, remainder = divmod(r-1, n)
    if remainder or not fmpz(r).is_prime() or binary_degree(r) != n:
        raise ValueError("expected a prime root order and its binary degree")
    # A generator modulo <2> has a nontrivial (r-1)/p power for every prime p | k.
    g = next(a for a in range(2, r)
             if all(pow(a, (r-1)//p, r) != 1 for p in prime_divisors(k)))
    labels = array('I', [k])*r
    representative = 1
    for orbit in range(k):
        u = representative
        for _ in range(n):
            if labels[u] != k:
                raise ArithmeticError("overlapping doubling cosets")
            labels[u] = orbit
            u = 2*u % r
        if u != representative:
            raise ArithmeticError("incorrect coset length")
        representative = representative*g % r

    one = (1 << k)-1
    columns = [0]*k
    # Column i gives T_0 T_i. When u = -1 the contribution is the scalar n mod 2.
    for u in range(1, r-1):
        columns[labels[u]] ^= 1 << labels[u+1]
    if n % 2:
        columns[labels[r-1]] ^= one

    def multiply_by_period(bits, i):
        remaining = rotate(bits, -i, k)
        value = 0
        while remaining:
            bit = remaining & -remaining
            value ^= columns[bit.bit_length()-1]
            remaining ^= bit
        return rotate(value, i, k)

    selected = one
    word = 0
    # Keep a nonempty joint eigenspace, preferring eigenvalue one at each step.
    for i in range(k):
        subset = multiply_by_period(selected, i)
        if subset:
            selected = subset
            word |= 1 << i
    if any(multiply_by_period(selected, i) != (selected if (word >> i) & 1 else 0)
           for i in range(k)) or len({rotate(word, i, k) for i in range(k)}) != k:
        raise ArithmeticError("could not isolate the period word and all its translates")
    return word, labels


def sparse_trace_prefix(n, word, labels, shift):
    k = (len(labels)-1)//n
    tap = 0
    for j in range(1, (n-1)//2+1, 2):
        trace = (word >> ((shift+labels[j]) % k)) & 1
        if tap == 0:
            if trace:
                tap = j
        elif trace != (j % tap == 0):
            return False
    return True


def prime_extension(ntl):
    # Orders through 256n+1 have already been excluded for prime n >= 13.
    flags = odd_prime_flags(16*301**3//5)
    small_primes = [p for p in range(3, 252, 2) if fmpz(p).is_prime()]
    small_factors = odd_small_factors(32767)
    if any(n >= 13 and r > 256*n+1 for n, r in small_composite_orders(300)):
        raise ArithmeticError("unexpected composite order in the extension")
    residual = []
    total = 0
    for k in range(258, 301, 2):
        if k % 8 == 4:
            continue
        for n, r in prime_degree_candidates(k, flags, small_primes):
            if n < 13:
                continue
            total += 1
            if not excludes_single_tap_prefix(n, r, k, small_factors):
                residual.append((n, r))
    if total != 28261 or len(residual) != len(PERIOD_WEIGHTS) or set(residual) != set(PERIOD_WEIGHTS):
        raise ArithmeticError(f"unexpected prime-degree sieve: {total}, {len(residual)}")
    for n, r in residual:
        word, labels = unit_trace_word(n, r)
        if word.bit_count() != PERIOD_WEIGHTS[n, r]:
            raise ArithmeticError(f"incorrect period weight in degree {n} at order {r}")
        if any(sparse_trace_prefix(n, word, labels, s) for s in range((r-1)//n)):
            raise ArithmeticError(f"a sparse trace prefix remains in degree {n} at order {r}")
    if ntl and cyclotomic_census(residual, ntl):
        raise ArithmeticError("NTL found an unexpected sparse prime-order factor")
    print("Excluded all 28,261 additional prime orders for prime degrees from 13 on.")


def composite_groups(ntl=None):
    groups = {}
    cases = set()
    for n in range(15, 257):
        if fmpz(n).is_prime():
            continue
        d = n//min(prime_divisors(n))
        if (1 << d)-1 > 300*n:
            continue
        for h in range(1, 300*n+1, 2):
            p, rem = divmod((1 << n)-1, h)
            if rem or not fmpz(p).is_prime():
                continue
            orders = [r for r in range(3, h+1, 2) if h % r == 0 and binary_degree(r) == n]
            groups[n, p] = orders
            cases.update((n, r) for r in orders)
    supports = flint_census(sorted(cases))
    if ntl:
        counts = {key: (sum(len(t) == 1 for t in rows), sum(len(t) == 3 for t in rows))
                  for key, rows in supports.items()}
        if cyclotomic_census(sorted(cases), ntl) != counts:
            raise ArithmeticError("NTL and FLINT disagree on a composite-degree root order")
    result = {}
    for (n, p), orders in groups.items():
        found = set().union(*(supports.get((n, r), set()) for r in orders))
        if found:
            result[n, p] = (sum(len(t) == 1 for t in found), sum(len(t) == 3 for t in found))
    expected = {(15, 31): (0, 4), (16, 17): (0, 10), (18, 73): (3, 6),
                (21, 337): (2, 0), (22, 683): (0, 2)}
    if len(groups) != 9 or len(cases) != 23 or result != expected:
        raise ArithmeticError(f"unexpected composite-degree exceptions: {result}")
    if supports[21, 49] != {(7,), (14,)} or supports[22, 6141] != {(2, 4, 11), (11, 18, 20)}:
        raise ArithmeticError("unexpected degree-21 or degree-22 supports")
    print("The five nonempty subgroups in composite degrees from 15 on have degrees 15, 16, 18, 21 and 22.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime-extension", action="store_true", help="also replay the prime-degree sieve")
    parser.add_argument("--ntl", metavar="CENSUS", help="independently factor all remaining cyclotomic cases")
    args = parser.parse_args()
    composite_groups(args.ntl)
    if args.prime_extension or args.ntl:
        prime_extension(args.ntl)
