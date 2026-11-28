"""Replay seven unit-trace probes on the known failures and the 28 largest tap families."""

import argparse
import csv
from hashlib import sha256
from itertools import combinations
from math import gcd

from flint import fq_default_ctx

from check_1229_tap_pencils import CAPACITY, DATA, census
from check_cubed_parity import polynomial
from check_degree_1229 import COFACTOR, GROUP, KNOWN, N, PRIMES


PROBES = (13, 27, 29, 31, 35, 41, 47)


def candidate_masks():
    supports, _, families = census()
    selected = {supports[i]: 0 for group in families.values() if len(group) > CAPACITY for i in group}
    if len(selected) != 443:
        raise ArithmeticError("unexpected number of surviving pencil members")
    with (DATA/"degree-1229-order-exceptions.csv").open(newline="") as source:
        for row in csv.DictReader(source):
            taps = tuple(int(row[k]) for k in "abc")
            mask = int(row["missing_mask"])
            if taps in selected or mask not in (1, 2):
                raise ArithmeticError("invalid known failure")
            selected[taps] = mask
    if len(selected) != 454:
        raise ArithmeticError("expected eleven exceptional supports")
    return selected


def odd_trace_word(z):
    """Bit k is the field trace of z^(2k+1), through the 63rd power."""
    step = z*z
    power = z
    word = 0
    for k in range(32):
        word |= int(power.trace()) << k
        power = power*step
    return word


def check_probes():
    multipliers = []
    for p in PRIMES:
        h = GROUP//p
        u = 1 + h*(-2*pow(h, -1, p) % p)
        if u % p != p-1 or u % h != 1 or pow(u, 2, GROUP) != 1:
            raise ArithmeticError(f"incorrect CRT involution at {p}")
        multipliers.append(u)
    if any(gcd(GROUP, j) != 1 for j in range(1, 64, 2)):
        raise ArithmeticError("expected unit trace positions")

    chosen = sum(1 << (j//2) for j in PROBES)
    missed_by_probe = [0]*32
    comparison_words = sha256()
    positive = 0
    for taps, mask in sorted(candidate_masks().items()):
        f = polynomial((0, *taps, N))
        if not f.is_irreducible():
            raise ArithmeticError(f"reducible polynomial at {taps}")
        z = fq_default_ctx(modulus=f, check_modulus=False).gen()
        base_word = odd_trace_word(z)
        for i, u in enumerate(multipliers):
            moved = z**u
            differences = odd_trace_word(moved) ^ base_word
            comparison_words.update(differences.to_bytes(4, "little"))
            failed = bool(mask & (1 << i))
            if (moved == z) != failed or (differences & chosen == 0) != failed:
                raise ArithmeticError(f"trace or order disagreement at taps {taps}, prime {PRIMES[i]}")
            if not failed:
                for k in range(32):
                    if not (differences >> k) & 1:
                        missed_by_probe[k] |= 1 << positive
                positive += 1

    if positive != 1805:
        raise ArithmeticError(f"unexpected number of positive tests: {positive}")
    # Independent NTL TraceVec/ProjectPowers replay, in tap order then prime order.
    if comparison_words.hexdigest() != "1e863712ff766157a05c9e488b3b1c037034a8e4d12978f950618ccd90f3d0bb":
        raise ArithmeticError("the 32-position comparisons disagree with the NTL replay")
    if any(a & b & c & d & e & f == 0 for a, b, c, d, e, f in combinations(missed_by_probe, 6)):
        raise ArithmeticError("six odd trace positions through 63 suffice")
    print("Seven trace comparisons classify all 1,816 tests on 454 reciprocal representatives.")
    print("No six odd positions through 63 detect every one of the 1,805 passes.")


def classify_multiplier(a):
    """A proposed extra symmetry of a surviving root must already give a factor of C."""
    a %= GROUP
    if gcd(a, GROUP) != 1:
        raise ValueError("the multiplier must be a unit modulo 2^1229-1")
    for h in range(N):
        difference = a - (1 << h)
        if difference % KNOWN:
            continue
        if not difference:
            return f"Ordinary Frobenius multiplier 2^{h}."
        divisor = gcd(difference, COFACTOR)
        if divisor == 1:
            return "Ruled out for every four-test survivor by the cofactor gcd."
        if divisor == COFACTOR:
            raise ArithmeticError("a non-Frobenius multiplier matched the entire group order")
        return f"Proper cofactor divisor {divisor}. Its effect on individual root orders is undetermined."
    return "Ruled out for every four-test survivor by the known prime factors."


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--multiplier", type=int, help="check a proposed common symmetry arithmetically")
    args = parser.parse_args()
    if args.multiplier is None:
        check_probes()
    else:
        print(classify_multiplier(args.multiplier))
