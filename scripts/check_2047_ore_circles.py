"""Check the degree-2047 character bound and reconstruct its two anchored matrices."""

import argparse
import csv
import gzip
import hashlib
import mmap
import struct
import subprocess
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


def check_archives(verifier, jobs, data):
    """Independently verify every field identity and the shared logarithms."""
    shared = []
    exponent_product = 1
    for q, m in FIELD_DEGREES.items():
        path = data / f"degree-2047-q{q}-projected.bin.gz"
        with gzip.open(path, "rb") as source:
            raw = source.read()
        magic, base, count = struct.unpack_from("<4sII", raw)
        expected = sum(c for d, c in irreducible_counts(m).items() if m % d == 0)
        if magic != b"G2O1" or base != q or count != expected or len(raw) != 12+232*count:
            raise ValueError(f"wrong or incomplete projected-log archive at {path}")
        subprocess.run([str(verifier), str(jobs)], input=raw, check=True)
        common = {}
        for offset in range(12, len(raw), 232):
            mask, = struct.unpack_from("<I", raw, offset)
            exponent = int.from_bytes(raw[offset+4:offset+232], "little")
            exponent_product = exponent_product*exponent % COFACTOR
            if mask in (2, 3, 7):
                common[mask] = exponent
        shared.append(common)
    if set(shared[0]) != {2, 3, 7} or shared[0] != shared[1]:
        raise ArithmeticError("the two archives disagree on their common factor base")
    if gcd(exponent_product, COFACTOR) != 1:
        raise ArithmeticError("a recorded exponent is a nonunit modulo the cofactor")
    print("Both archives passed direct powering and agree on the three common polynomials.")
    print("Every recorded exponent is coprime to the cofactor.")


def check_sparse_images(data):
    from check_cubed_parity import polynomial
    from check_ore_trace_coordinate import coordinate
    from check_trinomial_decimations import power_support

    # The reciprocal-seed power and its unit inverse connect taps 3 and 511.
    maps = coordinate(0x805)
    if maps["source_taps"] != [0, 3, DEGREE] or maps["target_taps"] != [0, 511, DEGREE]:
        raise ArithmeticError("unexpected reciprocal-seed pair")
    images = set()
    rows = []
    for tap in (3, 511, DEGREE-511, DEGREE-3):
        support = (0, tap, DEGREE)
        source = polynomial(support)
        rows.append((tap, 1, str(tap)))
        for exponent in (3, 5):
            target = power_support(support, exponent)
            image = polynomial(target)
            if (gcd(exponent, GROUP_ORDER) != 1 or len(target) != 5 or target in images
                    or not image.is_irreducible() or image.compose_mod(X**exponent, source) != 0):
                raise ArithmeticError(f"incorrect sparse image at tap {tap}, exponent {exponent}")
            images.add(target)
            rows.append((tap, exponent, " ".join(map(str, target[1:-1]))))
            print(f"Tap {tap}, root power {exponent}, pentanomial interior exponents {target[1:-1]}.")
    with (data / "degree-2047-sparse-witnesses.csv").open(newline="") as source:
        reader = csv.DictReader(source)
        if reader.fieldnames != ["source_tap", "power", "interior_exponents"]:
            raise ValueError("unexpected sparse-witness header")
        recorded = [(int(row["source_tap"]), int(row["power"]), row["interior_exponents"]) for row in reader]
    if rows != recorded:
        raise ArithmeticError("the published sparse witnesses differ from the power formulas")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", choices=FIELD_DEGREES, type=int)
    parser.add_argument("--relations", type=Path, help="binary output of gen_2047_ore_circles.cpp")
    parser.add_argument("--work-dir", type=Path, default=Path(".lake/ore-2047"))
    parser.add_argument("--fraction-bound", action="store_true",
                        help="compute the order bound from just the degree-18 field")
    parser.add_argument("--verify-logs", type=Path, metavar="NTL_CHECKER",
                        help="verify both published log archives by direct exponentiation")
    parser.add_argument("--data-dir", type=Path, default=Path(__file__).resolve().parents[1]/"data")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--sparse-images", action="store_true", help="verify four trinomials and their eight power images")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if (args.q is None) != (args.relations is None):
        parser.error("--q and --relations are used together")
    check_bound()
    if args.verify_logs:
        check_archives(args.verify_logs.resolve(), args.jobs, args.data_dir)
        print("The trinomial T^2047 + T^511 + 1 has order 2^2047-1 at its root.")
    if args.sparse_images:
        check_sparse_images(args.data_dir)
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
