"""Reconstruct the split norm circles and the q=512 logarithm matrix in quaternary model 21149."""

import argparse
import csv
import gzip
import json
import struct
from collections import Counter
from functools import lru_cache
from hashlib import sha256
from pathlib import Path

import numpy as np
from flint import fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx

from check_1229_height_two import binary_polynomial, bits, scalar
from check_degree_1229 import COFACTOR
from check_factor_base import DATA


Q, SIZE, MOD = 512, 1 << 18, 0x41403
ARCHIVE = DATA / "degree-1229-q512-quaternary-pencils.bin.gz"
ARCHIVE_HASH = "32c736037ae5561c0301157fa6ca4e06175702da94b3225c7501518765a5f479"


class Constants:
    def __init__(self):
        self.powers = np.empty(2*SIZE, dtype=np.int32)
        self.logs = np.full(SIZE, -1, dtype=np.int32)
        z = 1
        for j in range(SIZE-1):
            self.powers[j] = self.powers[j+SIZE-1] = z
            self.logs[z] = j
            z <<= 1
            if z & SIZE:
                z ^= MOD
        if z != 1 or self.logs[1:].min() < 0:
            raise ArithmeticError("incorrect multiplicative generator")
        self.bar = np.zeros(SIZE, dtype=np.int32)
        self.bar[1:] = self.powers[(Q*self.logs[1:]) % (SIZE-1)]
        self.omega = int(self.powers[(SIZE-1)//3])
        self.delta = int(self.mul(2, self.inv(2 ^ self.bar[2])))
        self.real = np.zeros(Q, dtype=np.int32)
        for j in range(9):
            self.real[1 << j:2 << j] = self.real[:1 << j] ^ self.powers[(Q+1)*j]
        self.index = np.full(SIZE, -1, dtype=np.int32)
        self.index[self.real] = np.arange(Q)
        if np.any(self.real != self.bar[self.real]) or len(np.unique(self.real)) != Q:
            raise ArithmeticError("incorrect nine-bit subfield basis")
        values = np.arange(SIZE, dtype=np.int32)
        squared = self.mul(values, values)
        self.fourth = self.mul(squared, squared)
        self.key = np.arange(SIZE, dtype=np.int32)
        z = self.key.copy()
        for _ in range(8):
            z = self.fourth[z]
            self.key = np.minimum(self.key, z)
        self.labels = np.unique(self.key)
        self.var = np.searchsorted(self.labels, self.key)
        if len(self.labels) != 29144:
            raise ArithmeticError("incorrect number of quaternary orbits")

    def mul(self, a, b):
        return np.where((a != 0) & (b != 0), self.powers[self.logs[a]+self.logs[b]], 0)

    def inv(self, a):
        if np.any(a == 0):
            raise ZeroDivisionError
        return self.powers[SIZE-1-self.logs[a]]


def census(f):
    # D(t)=0 is a real affine line in the center b, except at poles and r=bar(t).
    centers = np.arange(SIZE, dtype=np.int32)
    totals = np.zeros(SIZE*Q, dtype=np.uint8)
    h0 = [1, 1^f.omega, 1, f.omega, f.omega]
    h1 = [0, 1, 1]
    def evaluate(poly, t):
        x = np.zeros_like(t)
        for c in reversed(poly):
            x = f.mul(x, t) ^ c
        return x

    def accumulate(t, b, d, repeated):
        t, b, d, repeated = np.broadcast_arrays(t, b, d, repeated)
        if np.any(f.index[d] < 0):
            raise ArithmeticError("incidence enumeration left the real parameter line")
        addresses = b*Q+f.index[d]
        np.add.at(totals, addresses, 1)
        if not np.any(repeated):
            return
        t, b, d, addresses = (arr[repeated] for arr in (t, b, d, addresses))
        # Add the higher multiplicities using synthetic division on all the tangent incidences.
        p = [f.mul(b, h0[i] if i < len(h0) else 0) ^
             f.mul(d, h1[i] if i < len(h1) else 0) ^
             (h0[i-1] if 0 < i <= len(h0) else 0) ^
             f.mul(f.bar[b], h1[i-1] if 0 < i <= len(h1) else 0) for i in range(6)]
        active = np.ones(t.shape, dtype=bool)
        for power in range(1, 6):
            value = p[-1]
            quotient = []
            for c in reversed(p[:-1]):
                quotient.append(value)
                value = f.mul(value, t) ^ c
            active &= value == 0
            if power >= 2:
                np.add.at(totals, addresses[active], 1)
            if not np.any(active):
                break
            p = quotient[::-1]

    for start in range(0, SIZE, 256):
        t = centers[start:start+256]
        v = evaluate(h1, t)
        for pole in t[v == 0]:
            # h0 and h1 are coprime. Every circle with b=t has this pole in its numerator.
            derivative = evaluate(h0, pole) ^ f.mul(f.bar[pole], pole) ^ f.real
            accumulate(pole, pole, f.real, derivative == 0)
        t, v = t[v != 0], v[v != 0]
        r = f.mul(evaluate(h0, t), f.inv(v))
        rp = f.mul(evaluate([h0[1], 0, h0[3]], t)^r, f.inv(v))
        tr, alpha = f.mul(t, r), r^f.bar[t]
        for ti, ri, slope in zip(t[alpha == 0], r[alpha == 0], rp[alpha == 0]):
            d = f.mul(ti, ri)^f.mul(centers, ri)^f.mul(f.bar[centers], ti)
            accumulate(ti, centers, d, (ri^f.bar[centers]^f.mul(ti^centers,slope)) == 0)
        t, r, rp, tr, alpha = (v[alpha != 0, None] for v in (t, r, rp, tr, alpha))
        if not len(t):
            continue
        b = f.mul(f.mul(f.delta, tr^f.bar[tr]) ^ f.real, f.inv(alpha))
        d = tr ^ f.mul(b, r) ^ f.mul(f.bar[b], t)
        accumulate(t, b, d, (r^f.bar[b]^f.mul(t^b, rp)) == 0)
    centers = centers[f.key == centers]  # Test one center per F_4 orbit.
    kept = []
    all_count = 0
    for b in centers:
        good = np.flatnonzero(totals[b*Q:(b+1)*Q] == 5)
        good = good[f.real[good] != f.mul(b, f.bar[b])]
        if not len(good):
            continue
        length, z = 1, f.fourth[b]
        while z != b:
            length += 1
            z = f.fourth[z]
        all_count += length*len(good)
        d = f.real[good]
        least, z = d.copy(), d.copy()
        for _ in range(1, 9//length):
            for _ in range(length):
                z = f.fourth[z]
            least = np.minimum(least, z)
        kept.extend((int(b)*Q+good[least == d]).tolist())
    if all_count != 1118130 or len(kept) != 124252:
        raise ArithmeticError("incorrect smooth circle census")
    return np.asarray(kept, dtype="<u4").tobytes()


class Equations:
    def __init__(self, f):
        self.f = f
        self.k = fq_default_ctx(modulus=binary_polynomial(MOD, fmpz_mod_poly_ctx(2)), var="w")
        self.ring = fq_default_poly_ctx(self.k)
        self.t = self.ring.gen()
        w = scalar(f.omega, self.k)
        self.h0 = self.ring([1, w+1, 1, w, w])
        self.h1 = self.t**2+self.t
        points = np.arange(1, SIZE, dtype=np.int32)
        norms = f.index[f.mul(points, f.bar[points])]
        self.radii = [points[norms == i] for i in range(Q)]
        self.element = lru_cache(maxsize=8192)(lambda c: scalar(c, self.k))

    def row(self, code):
        f = self.f
        b, i = divmod(code, Q)
        d, bb = int(f.real[i]), int(f.bar[b])
        radius = f.index[d ^ int(f.mul(b, bb))]
        if radius == 0:
            raise ValueError("singular norm circle")
        p = (self.t+self.element(b))*self.h0+(self.element(bb)*self.t+self.element(d))*self.h1
        roots = p.roots()
        if sum(mult for _, mult in roots) != 5:
            raise ArithmeticError("a purported split numerator has a nonlinear factor")
        coeff = Counter(f.var[self.radii[radius] ^ bb].tolist())
        coeff[int(f.var[0])] += Q
        coeff[int(f.var[1])] += Q
        for root, mult in roots:
            coeff[int(f.var[f.bar[bits(root)]])] -= Q*mult
        return sorted((int(t), w) for t, w in coeff.items() if w)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true", help="repeat the incidence census of all nonsingular norm circles")
    parser.add_argument("--matrix", type=Path, help="write the checked matrix in the Wiedemann solver's binary format")
    parser.add_argument("--row", type=int, metavar="INDEX", help="export a zero-based archived row")
    parser.add_argument("--check-logs", action="store_true", help="check the published vector against every circle modulo C")
    parser.add_argument("--solution", type=Path, help="compare a phase-three binary solution with the published table")
    args = parser.parse_args()
    data = gzip.decompress(ARCHIVE.read_bytes())
    if len(data) != 124252*4 or sha256(data).hexdigest() != ARCHIVE_HASH:
        raise ArithmeticError("incorrect circle parameter archive")
    f = Constants()
    if args.rebuild:
        if census(f) != data:
            raise ArithmeticError("the reconstructed archive differs from the published identifiers")
    codes = np.frombuffer(data, dtype="<u4")
    if args.matrix or args.row is not None or args.check_logs:
        equations = Equations(f)
    if args.check_logs or args.solution:
        with gzip.open(DATA/"degree-1229-q512-quaternary-logs.csv.gz", "rt", newline="") as stream:
            table = list(csv.DictReader(stream))
        if [int(r["mask"], 0) for r in table] != f.labels.tolist():
            raise ArithmeticError("the exponent vector uses different orbit labels")
        logs = [int(r["exponent"]) for r in table]
        if args.solution:
            encoded = struct.pack("<I", len(logs))+b"".join(e.to_bytes(120, "little") for e in logs)
            if args.solution.read_bytes() != encoded:
                raise ArithmeticError("the independent solver output differs from the published exponents")
    if args.check_logs:
        for code in codes:
            if sum(w*logs[t] for t, w in equations.row(int(code))) % COFACTOR:
                raise ArithmeticError("a circle equation fails modulo the unfactored cofactor")
    if args.matrix:
        entry = struct.Struct("<Hi")
        with args.matrix.open("wb") as stream:
            stream.write(struct.pack("<II", len(f.labels), len(codes)))
            stream.write(f.labels.astype("<u4").tobytes())
            for code in codes:
                row = equations.row(int(code))
                stream.write(struct.pack("<H", len(row)))
                stream.write(b"".join(entry.pack(t, w) for t, w in row))
    if args.row is not None:
        if not 0 <= args.row < len(codes):
            parser.error("row index outside the archive")
        code = int(codes[args.row])
        b, i = divmod(code, Q)
        print(json.dumps({"b":hex(b), "d":hex(int(f.real[i])),
                          "coefficients":[[hex(int(f.labels[t])), w] for t,w in equations.row(code)]}))
    else:
        print("Verified 124,252 orbit representatives on 29,144 labels in model 21149.")


if __name__ == "__main__":
    main()
