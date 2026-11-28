"""Classify prime-degree binary irreducibles of weight at most five and order at most K*n+1.

Use python-flint and the --census executable compiled from cyclotomic_weight_census.cpp.
The degree cutoff follows from the lattice bound for normalized support.
"""

import argparse
import json
import subprocess
from itertools import combinations
from math import gcd, isqrt

from flint import fmpz, nmod_poly


def odd_prime_flags(limit):
    """Index i represents the odd integer 2*i+1."""
    flags = bytearray([1]) * ((limit + 1) // 2)
    flags[0] = 0
    for p in range(3, isqrt(limit) + 1, 2):
        if flags[p // 2]:
            first = p * p // 2
            flags[first::p] = bytes(len(flags[first::p]))
    return flags


def prime_degree_candidates(k, flags, small_primes):
    limit = 16 * (k + 1)**3 // 5
    allowed = flags[:(limit + 1) // 2]
    for i in range(4):
        if (k * (2 * i + 1) + 1) % 8 not in (1, 7):
            allowed[i::4] = bytes(len(allowed[i::4]))
    # Remove small factors of k*n+1, retaining the case in which k*n+1 is the prime itself.
    for p in small_primes:
        if k % p == 0:
            continue
        first = (-(k + 1) * pow(2 * k, -1, p)) % p
        if k * (2 * first + 1) + 1 == p:
            first += p
        allowed[first::p] = bytes(len(allowed[first::p]))
    i = allowed.find(1)
    while i >= 0:
        n = 2 * i + 1
        ell = k * n + 1
        if 16 * ell**3 >= 5 * n**4 and pow(2, n, ell) == 1 and fmpz(ell).is_prime():
            yield n, ell
        i = allowed.find(1, i + 1)


def odd_small_factors(limit):
    factors = [0] * ((limit + 1) // 2)
    for p in range(3, isqrt(limit) + 1, 2):
        if factors[p // 2]:
            continue
        for j in range(p * p, limit + 1, 2 * p):
            if not factors[j // 2]:
                factors[j // 2] = p
    return factors


def excludes_single_tap_prefix(n, ell, k, small_factors):
    """A gcd of one in each doubling coset contradicts a trace prefix with at most one tap."""
    # Raising to n has kernel <2> in the cyclic group of order k*n.
    classes = [1]
    representatives = {}
    complete = 0
    for j in range(1, (n - 1) // 2 + 1, 2):
        index = j // 2
        if index:
            p = small_factors[index] if index < len(small_factors) else 0
            if p:
                label = classes[p // 2] * classes[(j // p) // 2] % ell
            else:
                label = pow(j, n, ell)
            classes.append(label)
        label = classes[index]
        old = representatives.get(label, 0)
        new = gcd(old, j)
        if old != 1:
            representatives[label] = new
            if new == 1:
                complete += 1
                if complete == k:
                    return True
    return False


def small_composite_orders(multiple):
    for n in range(3, multiple // 4 + 1, 2):
        if not fmpz(n).is_prime():
            continue
        for order in range((2 * n + 1)**2, multiple * n + 2, 2):
            if pow(2, n, order) == 1 and not fmpz(order).is_prime():
                yield n, order


def cyclotomic_census(cases, backend):
    inputs = "".join(f"{n} {order}\n" for n, order in cases)
    result = subprocess.run([backend, "--sparse-factors"], input=inputs, text=True,
                            stdout=subprocess.PIPE, check=True)
    found = {}
    for line in result.stdout.splitlines():
        row = json.loads(line)
        key = row["degree"], row["order"]
        weights = {int(w): v for w, v in row["weights"].items()}
        if key in found or sum(weights.values()) * key[0] != fmpz(key[1]).euler_phi():
            raise ArithmeticError(f"incomplete cyclotomic census for {key}")
        found[key] = tuple(weights.get(w, 0) for w in (3, 5))
    if set(found) != set(cases):
        raise ArithmeticError("missing or extra cyclotomic orders")
    return {key: pair for key, pair in found.items() if any(pair)}


def direct_small_degrees(multiple):
    """Independently count all trinomials and pentanomials in the five exceptional degrees."""
    x = nmod_poly([0, 1], 2)
    counts = {}
    for n in (2, 3, 5, 7, 11):
        full = 2**n - 1
        for size in (1, 3):
            for taps in combinations(range(1, n), size):
                f = x**n + sum(x**e for e in taps) + 1
                # In prime degree, all factors of X^(2^n)-X have degree one or n.
                if x.pow_mod(2**n, f) != x:
                    continue
                order = full
                for p, _ in fmpz(full).factor():
                    p = int(p)
                    while order % p == 0 and x.pow_mod(order // p, f) == 1:
                        order //= p
                if order <= multiple * n + 1:
                    key = n, order
                    counts.setdefault(key, [0, 0])[(size - 1) // 2] += 1
    return {key: tuple(value) for key, value in counts.items()}


def check_first_order():
    """Above degree 31 the linear bound already exceeds 8191."""
    for n in (13, 17, 19, 23, 29, 31):
        full = (1 << n) - 1
        if any(full % r == 0 for r in range(256 * n + 3, 8191, 2)):
            raise ArithmeticError(f"possible smaller order in degree {n}")
    x = nmod_poly([0, 1], 2)
    witness = x**13 + x**5 + x**2 + x + 1
    if not fmpz(8191).is_prime() or x.pow_mod(8191, witness) != 1:
        raise ArithmeticError("the example of order 8191 failed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", required=True)
    parser.add_argument("--multiple", type=int, default=256)
    args = parser.parse_args()
    if args.multiple < 2:
        parser.error("the order multiple must be at least two")
    limit = 16 * (args.multiple + 1)**3 // 5
    flags = odd_prime_flags(limit)
    small_primes = [p for p in range(3, 252, 2) if fmpz(p).is_prime()]
    small_factors = odd_small_factors(32767)
    composite = list(small_composite_orders(args.multiple))
    cases = [(2, 3), *composite]
    primes = excluded = 0
    for k in range(2, args.multiple + 1, 2):
        if k % 8 == 4:
            continue
        for n, ell in prime_degree_candidates(k, flags, small_primes):
            primes += 1
            if excludes_single_tap_prefix(n, ell, k, small_factors):
                excluded += 1
            else:
                cases.append((n, ell))
    print(f"{primes} prime orders in odd prime degrees, {excluded} excluded by traces, "
          f"{primes - excluded} sent to the factor census. "
          f"{len(composite)} composite orders.", flush=True)
    sparse = cyclotomic_census(sorted(cases), args.census)
    direct = direct_small_degrees(args.multiple)
    if {key: value for key, value in sparse.items() if key[0] < 13} != direct:
        raise ArithmeticError("disagreement with direct sparse polynomial enumeration")
    if args.multiple <= 256 and sparse != direct:
        raise ArithmeticError("unexpected sparse factor in a prime degree above eleven")
    for (n, order), (tri, penta) in sorted(sparse.items()):
        print(f"Degree {n}, order {order}: {tri} trinomials and {penta} pentanomials.")
    if args.multiple == 256:
        check_first_order()
        print("The smallest order in any prime degree at least 13 is 8191, attained in degree 13.")


if __name__ == "__main__":
    main()
