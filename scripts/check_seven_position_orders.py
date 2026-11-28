"""Verify the finite part of the seven-position theorem in every degree 7*q^b.

Run with uv run --no-project --with python-flint==0.9.0 python
scripts/check_seven_position_orders.py. The exhaustive trace check uses a C++17 compiler.
"""

import subprocess
from itertools import count, permutations
from math import gcd
from pathlib import Path
from tempfile import TemporaryDirectory

from flint import fmpz, nmod_poly


def frobenius_cost(ell, z, k):
    """Minimize the cost of a signed odd ratio up to the proven coset bound."""
    bound = 2 * (k * k - 1)
    best = bound + 1
    for a in range(3, bound + 1, 2):
        for b in range(1, min(a - 1, bound // a) + 1, 2):
            if gcd(a, b) != 1 or a % ell == 0 or b % ell == 0:
                continue
            left, right = pow(a, z, ell), pow(b, z, ell)
            if left == right:
                best = min(best, a * b)
            elif (left + right) % ell == 0:
                best = min(best, 2 * a * b)
    assert best <= bound
    return best


def residual_lengths():
    """Apply the determinant bound and the short Frobenius ratio for every possible k."""
    cases = []
    for k in (2, 4, 6):
        bound = 2 * (k * k - 1)
        for q in range(11, 6 * bound + 1, 2):
            if not fmpz(q).is_prime():
                continue
            for b in count(2):
                z = q**b
                ell = k * z + 1
                if ell > (6 * k + 1)**9 or (k == 2 and ell > 24**2):
                    break
                if ell % 8 not in (1, 7) or not fmpz(ell).is_prime():
                    continue
                if pow(2, z, ell) != 1 or pow(2, z // q, ell) == 1:
                    continue
                cost = frobenius_cost(ell, z, k)
                if q <= 6 * cost:
                    assert k == 6 and q > cost
                    cases.append((q, b, ell, cost))
    return cases


def check_inverse_minor(ell, z, q):
    """A trace test for the seven exponents in the product at a root and its inverse."""
    columns = (0, 1, 5, 6, 7, 11, 12)
    generator = pow(2, z // q, ell)
    rows = [pow(generator, r, ell) for r in range(len(columns))]
    terms = set()
    for perm in permutations(columns):
        exponent = sum(u * e for u, e in zip(rows, perm)) % ell
        terms.symmetric_difference_update((exponent,))

    classes = {}
    for a in range(1, ell):
        residue = pow(a, z, ell)
        if residue not in classes:
            classes[residue] = 1 << len(classes)
        if len(classes) == 6:
            break
    assert len(classes) == 6
    # Each viable trace assignment has odd weight because the six periods sum to one.
    possible = {t for t in range(64) if t.bit_count() % 2}
    for shift in range(256):
        mask = 0
        for e in terms:
            exponent = (e + shift) % ell
            mask ^= classes[pow(exponent, z, ell)] if exponent else 63
        possible = {t for t in possible if (t & mask).bit_count() % 2 == 0}
        if not possible:
            return len(terms), shift + 1
    raise ArithmeticError("inconclusive determinant for the inverse relation")


def main():
    cases = residual_lengths()
    assert cases == [(11, 2, 727, 6), (11, 8, 1286153287, 10), (31, 4, 5541127, 6),
                     (47, 4, 29278087, 15), (79, 2, 37447, 15)]
    with TemporaryDirectory() as work:
        checker = Path(work) / "seven_position_traces"
        source = Path(__file__).with_name("check_seven_position_traces.cpp")
        subprocess.run(["c++", "-O3", "-std=c++17", str(source), "-o", str(checker)], check=True)
        for q, b, ell, cost in cases:
            z = q**b
            if ell > 24**6:
                assert q == 11 and 2 * 5 < q and (ell - 1) // z == 6
                terms, shifts = check_inverse_minor(ell, z, q)
                assert (terms, shifts) == (5040, 5)
                print(f"q={q}, b={b}, length {ell}: inverse minor certified by {shifts} traces.")
                continue
            generator = pow(2, z // q, ell)
            count_columns = 0
            max_shifts = 0
            for j in range(2, 7):
                if q > j * cost:
                    continue
                for i in range(1, j // 2 + 1):
                    if gcd(i, j) != 1:
                        continue
                    inputs = f"{ell} {q} {generator} {i} {j}\n"
                    run = subprocess.run([checker], input=inputs, stdout=subprocess.PIPE,
                                         text=True, check=True)
                    length, middle, span, tested, shifts = map(int, run.stdout.split())
                    assert (length, middle, span, tested) == (ell, i, j, ell - 3)
                    assert 0 < shifts <= 256
                    count_columns += tested
                    max_shifts = max(max_shifts, shifts)
            print(f"q={q}, b={b}, length {ell}: {count_columns} fourth columns, "
                  f"at most {max_shifts} traces.")
    x = nmod_poly([0, 1], 2)
    f = x**7 + x**3 + x**2 + x + 1
    assert x.pow_mod(127, f) == 1 and f(1) == 1
    print("The order-127 example and all five residual lengths pass.")


if __name__ == "__main__":
    main()
