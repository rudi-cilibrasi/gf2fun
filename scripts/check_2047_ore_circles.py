"""Check the degree-2047 character bound and reconstruct its two anchored matrices."""

import argparse
import hashlib
import mmap
import struct
from collections import Counter
from math import gcd, prod
from pathlib import Path

from flint import fmpz
from check_cubed_parity import BINARY, X
from check_factor_base import irreducible_counts, moment_bound, ratio_bound
from check_ore_2047 import KNOWN_PRIMES


DEGREE = 2047
GROUP_ORDER = (1 << DEGREE) - 1
KNOWN = prod(KNOWN_PRIMES)
COFACTOR = GROUP_ORDER // KNOWN
FIELD_DEGREES = {512: 18, 1024: 20}
# Counts of all circles, distinct normalized rows, and SHA-256 of selected entries.
MATRICES = {
    512: (67314, 66946, "ad5fcb9e774429a835bc7139d387ec60200c9a5743445c5de47c58983d1b2cfc"),
    1024: (83168, 82532, "d381399bcdec2256e379bc737cbd9933c3b93da8b12f5a9affbee539b000b999"),
}


def check_bound():
    if (KNOWN * COFACTOR != GROUP_ORDER or gcd(KNOWN, COFACTOR) != 1
            or not all(fmpz(p).is_prime() for p in KNOWN_PRIMES)
            or gcd(COFACTOR, ((1 << 23)-1)*((1 << 89)-1)) != 1):
        raise ValueError("invalid degree-2047 cofactor decomposition")
    x = X
    f = x**2047 + x**511 + 1
    if (not f.is_irreducible() or x.pow_mod(GROUP_ORDER, f) != 1
            or any(x.pow_mod(GROUP_ORDER//p, f) == 1 for p in KNOWN_PRIMES)):
        raise ArithmeticError("irreducibility or a known order check failed")
    floor = 1_000_000
    if any(COFACTOR % d == 0 for d in range(4095, floor+1, 4094)):
        raise ArithmeticError("a small divisor of the cofactor was found")
    counts = {d: count for d, count in irreducible_counts(20).items() if 18 % d == 0 or 20 % d == 0}
    bound = moment_bound(counts, floor, 63)
    if sum(counts.values()) != 67087 or bound <= DEGREE-2:
        raise ArithmeticError("the two factor bases do not reach the character bound")
    print(f"Seven prime-index powers passed; index divides the {len(str(COFACTOR))}-digit cofactor.")
    print(f"The {sum(counts.values())} polynomial values give {bound} > {DEGREE-2}.")


def pack(q, path, folder):
    import numpy as np
    m = FIELD_DEGREES[q]
    expected = {d: count for d, count in irreducible_counts(m).items() if m % d == 0}
    row_count, distinct, digest = MATRICES[q]
    dtype = np.dtype([("idx", "<u2"), ("coeff", "<i4")])

    def entries(row, divisor):
        coefficients = row["coeff"] // divisor
        packed = row["idx"].astype("<u4") | (coefficients.astype("<u4") << 16)
        if not np.all((packed >> 16).astype(np.int16) == coefficients):
            raise OverflowError("a normalized coefficient exceeds the packed range")
        return packed

    with path.open("rb") as source, mmap.mmap(source.fileno(), 0, access=mmap.ACCESS_READ) as data:
        n, count = struct.unpack_from("<II", data)
        masks = np.frombuffer(data, dtype="<u4", count=n, offset=8).copy()
        labels = list(map(int, masks))
        if (count != row_count or n != len(set(labels)) or labels[0] != 2
                or Counter(mask.bit_length()-1 for mask in labels) != expected
                or not all(BINARY([(mask >> k) & 1 for k in range(mask.bit_length())]).is_irreducible()
                           for mask in labels)):
            raise ValueError("unexpected circle count or incomplete binary factor base")
        offset = 8 + 4*n
        by_hash = {}
        for i in range(count):
            length, = struct.unpack_from("<H", data, offset)
            offset += 2
            row = np.frombuffer(data, dtype=dtype, count=length, offset=offset)
            if (not length or row["idx"][-1] >= n or np.any(row["coeff"] == 0)
                    or np.any(row["idx"][1:] <= row["idx"][:-1])):
                raise ValueError(f"invalid circle row {i}")
            divisor = int(np.gcd.reduce(row["coeff"]))
            if gcd(divisor, COFACTOR) != 1:
                raise ArithmeticError("nonunit row normalization")
            key = hashlib.sha256(entries(row, divisor).tobytes()).digest()
            by_hash.setdefault(key, (offset, length, divisor))
            offset += 6*length
        if len(by_hash) != distinct or offset != len(data):
            raise ValueError("incorrect set of normalized rows")
        selected = []
        pointers = [0]
        for key in sorted(by_hash)[:n-1]:
            offset, length, divisor = by_hash[key]
            row = np.frombuffer(data, dtype=dtype, count=length, offset=offset)
            selected.append(entries(row, divisor))
            pointers.append(pointers[-1] + length)
        del row
    selected.append(np.array([1 << 16], dtype="<u4"))  # Anchor at P(T) = T.
    pointers.append(pointers[-1]+1)
    packed = np.concatenate(selected).astype("<u4", copy=False)
    if hashlib.sha256(packed.tobytes()).hexdigest() != digest:
        raise ArithmeticError("selected relation entries differ from the reference matrix")
    folder.mkdir(parents=True, exist_ok=True)
    np.save(folder / f"q{q}-masks.npy", masks)
    np.save(folder / f"q{q}-ptr.npy", np.array(pointers, dtype="<u4"))
    np.save(folder / f"q{q}-entries.npy", packed)
    print(f"q={q}: {count} circles, {n} rows and columns, {len(packed)} nonzero entries.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", choices=FIELD_DEGREES, type=int)
    parser.add_argument("--relations", type=Path, help="binary output of gen_2047_ore_circles.cpp")
    parser.add_argument("--work-dir", type=Path, default=Path(".lake/ore-2047"))
    parser.add_argument("--fraction-bound", action="store_true",
                        help="compute the order bound from just the degree-18 field")
    args = parser.parse_args()
    if (args.q is None) != (args.relations is None):
        parser.error("--q and --relations are used together")
    check_bound()
    if args.fraction_bound:
        counts = {d: n for d, n in irreducible_counts(18).items() if 18 % d == 0}
        lower = ratio_bound(DEGREE, counts)
        if not (1 << 1083) < lower < (1 << 1084):
            raise ArithmeticError("unexpected degree-18 reduced-fraction count")
        print("The degree-18 factor base alone gives root order greater than 2^1083.")
    if args.q:
        pack(args.q, args.relations, args.work_dir)


if __name__ == "__main__":
    main()
