"""Search for sparse primitive polynomials and emit Lean-checkable witnesses.

Usage: python3 scripts/make_witnesses.py [--start FIRST] [--factor-table JSON] LAST
SymPy is used only during discovery. Lean checks the resulting certificates.
"""

import argparse
import json
from functools import cache
from itertools import count
from math import prod

from sympy import divisors, factorint, isprime

try:
    from flint import fmpz
except ImportError:
    fmpz = None


@cache
def prime_factors(number):
    if fmpz is not None:
        return tuple(sorted(int(p) for p, e in fmpz(number).factor() for _ in range(e)))
    return tuple(sorted(int(p) for p, e in factorint(number).items() for _ in range(e)))


@cache
def cyclotomic_at_two(n):
    return ((1 << n) - 1) // prod(cyclotomic_at_two(d) for d in divisors(n) if d < n)


def mersenne_factors(n):
    return tuple(sorted(p for d in divisors(n) for p in prime_factors(cyclotomic_at_two(d))))


def table_factors(n, table):
    if str(n) not in table:
        return mersenne_factors(n)
    factors = tuple(sorted(table[str(n)]))
    if prod(factors) != (1 << n) - 1 or not all(isprime(p) for p in set(factors)):
        raise ValueError(f"incomplete prime factorization of 2^{n} - 1 in the table")
    return factors


def remainder(value, modulus):
    while value.bit_length() >= modulus.bit_length():
        value ^= modulus << (value.bit_length() - modulus.bit_length())
    return value


def mask_product(a, b):
    if a.bit_length() < b.bit_length():
        a, b = b, a
    result = 0
    while b:
        bit = b & -b
        result ^= a << (bit.bit_length() - 1)
        b ^= bit
    return result


def exact_quotient(f, g):
    quotient = 0
    while f.bit_length() >= g.bit_length():
        shift = f.bit_length() - g.bit_length()
        quotient ^= 1 << shift
        f ^= g << shift
    assert f == 0
    return quotient


def gcd(left, right):
    while right:
        left, right = right, remainder(left, right)
    return left


# In characteristic two, squaring inserts a zero bit between consecutive bits.
SQUARE_BYTES = [
    sum(((byte >> i) & 1) << (2 * i) for i in range(8)).to_bytes(2, "little")
    for byte in range(256)
]


def square_mod(value, modulus):
    digits = value.to_bytes((value.bit_length() + 7) // 8, "little")
    return remainder(int.from_bytes(b"".join(SQUARE_BYTES[b] for b in digits), "little"), modulus)


def x_power(exponent, modulus):
    value = 1
    for bit in bin(exponent)[2:]:
        value = square_mod(value, modulus)
        if bit == "1":
            value = remainder(value << 1, modulus)
    return value


def primitive(n, mask, primes):
    # Reject small factors early. The two order checks decide primitivity.
    x = remainder(2, mask)
    frobenius = x
    for _ in range(min(8, n // 2)):
        frobenius = square_mod(frobenius, mask)
        if gcd(frobenius ^ x, mask) != 1:
            return False
    order = (1 << n) - 1
    return x_power(order, mask) == 1 and all(x_power(order // p, mask) != 1 for p in set(primes))


def candidates(n):
    ends = (1 << n) | 1
    if n < 5:
        if n == 1:
            yield ends, None
        for a in range(1, n):
            yield ends | (1 << a), None
        return
    # Odd sums give squarefree candidates. Also try the other sums.
    for first_sum in (3, 4):
        for top in range(first_sum, n, 2):
            for u in range(1, (top + 1) // 2):
                v = top - u
                yield ends | (1 << top) | (1 << u) | (1 << v), (u, v)


def power_blocks(exponent, modulus, bits):
    """Return the residue and the previous residues, from last to first."""
    value = 1
    previous = []
    width = ((exponent.bit_length() + bits - 1) // bits) * bits
    for shift in range(width - 1, -1, -1):
        if (shift + 1) % bits == 0:
            previous.append(value)
        value = square_mod(value, modulus)
        if (exponent >> shift) & 1:
            value = remainder(value << 1, modulus)
    return value, previous[::-1]


def emit_block_witness(n, row, bits):
    mask, (u, v), factors = row
    print(f"\nprivate abbrev modulus := productMask {n} {u} {v}")
    print("private noncomputable abbrev root := AdjoinRoot.root (decode modulus)")
    for p in [1, *sorted(set(factors))]:
        value, blocks = power_blocks(((1 << n) - 1) // p, mask, bits)
        if (value == 1) != (p == 1):
            raise ValueError(f"unexpected residue in degree {n} for divisor {p}")
        exponent = f"(2 ^ {n} - 1)" if p == 1 else f"((2 ^ {n} - 1) / {p})"
        relation = "= 1" if p == 1 else "≠ 1"
        print(f"\nprivate theorem power{p} : root ^ {exponent} {relation} :=")
        if p == 1:
            print(f"  root_pow_one_of_blocks {n} modulus {bits} _ [")
        else:
            print(f"  root_pow_ne_one_of_blocks {n} modulus {bits} _ 0x{value:x} [")
        print(",\n".join(f"    0x{a:x}" for a in blocks) + "] (by decide +kernel)")
        if p != 1:
            print("    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)")
    print(f"\ntheorem primitiveProduct_{n}_{u}_{v} : Primitive (productCandidate {n} {u} {v}) := by")
    print("  rw [← decode_productMask]")
    print(f"  exact primitive_of_certified_powers (n := {n}) (by decide) (by decide +kernel) power1 [")
    print(",\n".join(f"    ⟨p{p}, power{p}⟩" for p in factors) + "] (by decide +kernel)")
    print("\nend GF2Sparse")


def emit(limit, start=1, *, factor_table=None, block_size=None):
    rows = []
    for n in range(start, limit + 1):
        factors = table_factors(n, factor_table or {})
        for mask, shape in candidates(n):
            if primitive(n, mask, factors):
                rows.append((mask, shape, factors))
                break
        else:
            raise ValueError(f"exhausted the chosen family in degree {n}")

    # Postorder the Lucas proof tree and share each proof across all rows.
    proofs = {}

    def certify(p):
        if p in proofs:
            return
        if p < 1024:
            proofs[p] = f"⟨{p}, by norm_num1⟩"
            return
        factors = prime_factors(p - 1)
        for q in factors:
            certify(q)
        a = next(a for a in count(2) if all(pow(a, (p - 1) // q, p) != 1 for q in set(factors)))
        proofs[p] = f"lucasPrime {p} {a} {factor_refs(factors)} (by decide +kernel)"

    def factor_refs(factors):
        return "[" + ", ".join(f"p{q}" for q in factors) + "]"

    for _, _, factors in rows:
        for q in factors:
            certify(q)

    print("import GF2Sparse.Table\n")
    print("/-! Generated by scripts/make_witnesses.py. Bit i is the coefficient of X^i. -/\n")
    print("namespace GF2Sparse\n")
    print("set_option maxRecDepth 8192")
    if limit > 256:
        print("set_option maxHeartbeats 2000000")
    print()
    for p, proof in proofs.items():
        print(f"private def p{p} : ProvenPrime := {proof}")
    if block_size is not None:
        emit_block_witness(start, rows[0], block_size)
        return
    if start == 1:
        print("\nprivate def smallRows : List Row := [")
        for i, (mask, _, factors) in enumerate(rows[:4], start=1):
            suffix = "," if i < 4 else "]"
            print(f"  (0x{mask:x}, {factor_refs(factors)}){suffix} -- degree {i}")
    print()
    first = max(5, start)
    for i, (_, (u, v), factors) in enumerate(rows[first - start:], start=first):
        print(f"private def row{i} := productEntry {i} {u} {v} {factor_refs(factors)} (by decide +kernel)")
    print("\nprivate def productRows : List {k : ℕ // HasPrimitiveProduct k} := [")
    for i in range(first, limit + 1, 10):
        stop = min(i + 10, limit + 1)
        suffix = "," if stop <= limit else "]"
        print("  " + ", ".join(f"row{j}" for j in range(i, stop)) + suffix)
    name = f"upto_{limit}" if start == 1 else f"{start}_to_{limit}"
    print(f"\ntheorem primitiveProduct_{name} (n : ℕ) (hn : {first} ≤ n) (hmax : n ≤ {limit}) :")
    print("    HasPrimitiveProduct n :=")
    print(f"  covers_range productRows {first} {limit - first + 1} (by decide +kernel) n hn (by omega)")
    if start > 1:
        print("\nend GF2Sparse")
        return
    print(f"\ntheorem sparsePrimitive_upto_{limit} (n : ℕ) (hn : 0 < n) (hmax : n ≤ {limit}) :")
    print("    HasSparsePrimitive n := by")
    print("  by_cases h : n < 5")
    print("  · exact checkRows_sound smallRows 1 (by decide +kernel) n hn h")
    print(f"  · exact (primitiveProduct_upto_{limit} n (by omega) hmax).sparse\n\nend GF2Sparse")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", type=int)
    parser.add_argument("--start", type=int, default=1, help="first degree of a separate certificate table")
    parser.add_argument("--factor-table", type=argparse.FileType("r"),
                        help="optional Cunningham table2-_data JSON or a map of degrees to prime factors")
    parser.add_argument("--block-size", type=int,
                        help="emit a single explicit witness with this many bits per powering block")
    args = parser.parse_args()
    if args.limit < 5:
        parser.error("the product-family table starts in degree 5")
    if args.start != 1 and not 5 <= args.start <= args.limit:
        parser.error("start must be 1 or between 5 and the final degree")
    if args.block_size is not None and (args.block_size < 1 or args.start != args.limit):
        parser.error("--block-size requires a positive block size and --start equal to the final degree")
    table = {}
    if args.factor_table:
        with args.factor_table as source:
            table = json.load(source)
        table = table.get("table2-_data", table)
    emit(args.limit, args.start, factor_table=table, block_size=args.block_size)
