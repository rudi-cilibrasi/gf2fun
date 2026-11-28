"""Reconstruct the q=512 and q=1024 norm-circle matrices in quaternary model 21149."""

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


PARAMETERS = {
    512: (0x41403, 29144, 1118130, 124252, "32c736037ae5561c0301157fa6ca4e06175702da94b3225c7501518765a5f479"),
    1024: (0x100009, 104968, 1610823, 172222, "7f42e6c50504eafd46a38990f4509adbfa96ee963739cd12d16ca4d8da920b05"),
}


class Constants:
    def __init__(self, q):
        self.q, self.size = q, q*q
        self.m = q.bit_length()-1
        self.stretch = q//512
        self.modulus, labels, self.split, self.rows, self.digest = PARAMETERS[q]
        size = self.size
        self.powers = np.zeros(2*size, dtype=np.int32)
        self.logs = np.full(size, -1, dtype=np.int32)
        z = 1
        for j in range(size-1):
            self.powers[j] = self.powers[j+size-1] = z
            self.logs[z] = j
            z <<= 1
            if z & size:
                z ^= self.modulus
        if z != 1 or self.logs[1:].min() < 0:
            raise ArithmeticError("incorrect multiplicative generator")
        self.bar = np.zeros(size, dtype=np.int32)
        self.bar[1:] = self.powers[(q*self.logs[1:]) % (size-1)]
        self.omega = int(self.powers[(size-1)//3])
        self.delta = int(self.mul(2, self.inv(2 ^ self.bar[2])))
        self.real = np.zeros(q, dtype=np.int32)
        for j in range(self.m):
            self.real[1 << j:2 << j] = self.real[:1 << j] ^ self.powers[(q+1)*j]
        self.index = np.full(size, -1, dtype=np.int32)
        self.index[self.real] = np.arange(q)
        if np.any(self.real != self.bar[self.real]) or len(np.unique(self.real)) != q:
            raise ArithmeticError("incorrect subfield basis")
        values = np.arange(size, dtype=np.int32)
        squared = self.mul(values, values)
        self.fourth = self.mul(squared, squared)
        self.key = values.copy()
        z = self.key.copy()
        for _ in range(1, self.m):
            z = self.fourth[z]
            self.key = np.minimum(self.key, z)
        self.labels = np.unique(self.key)
        self.var = np.searchsorted(self.labels, self.key)
        if len(self.labels) != labels:
            raise ArithmeticError("incorrect number of quaternary orbits")

    def mul(self, a, b):
        return np.where((a != 0) & (b != 0), self.powers[self.logs[a]+self.logs[b]], 0)

    def inv(self, a):
        if np.any(a == 0):
            raise ZeroDivisionError
        return self.powers[self.size-1-self.logs[a]]

    def sqrt(self, a):
        # Divide the nonzero exponent by two in the odd-order multiplicative group.
        e = self.logs[a]
        return np.where(a != 0, self.powers[(e+(e & 1)*(self.size-1))//2], 0)

    def twist(self, a):
        return a if self.stretch == 1 else self.mul(a, a)


def census(f):
    # D(t)=0 is a real affine line in the center b, except at poles and r=bar(t).
    q, s = f.q, f.stretch
    degree = 4+s
    centers = np.arange(f.size, dtype=np.int32)
    totals = np.zeros(f.size*q, dtype=np.uint8)
    omega = int(f.twist(f.omega))
    h0 = [1, 1^omega, 1, omega, omega]
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
        addresses = b*q+f.index[d]
        np.add.at(totals, addresses, 1)
        if not np.any(repeated):
            return
        t, b, d, addresses = (arr[repeated] for arr in (t, b, d, addresses))
        # Add the higher multiplicities using synthetic division on all the tangent incidences.
        bs, ds, bars = f.twist(b), f.twist(d), f.twist(f.bar[b])
        p = [f.mul(bs, h0[i] if i < len(h0) else 0) ^
             f.mul(ds, h1[i] if i < len(h1) else 0) ^
             (h0[i-s] if s <= i < s+len(h0) else 0) ^
             f.mul(bars, h1[i-s] if s <= i < s+len(h1) else 0) for i in range(degree+1)]
        active = np.ones(t.shape, dtype=bool)
        for power in range(1, degree+1):
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

    def tangent(t, b, r, slope):
        if s == 2:
            return (t == b) | (slope == 0)
        return (r ^ f.bar[b] ^ f.mul(t^b, slope)) == 0

    for start in range(0, f.size, 256):
        t = centers[start:start+256]
        v = evaluate(h1, t)
        for pole in t[v == 0]:
            # h0 and h1 are coprime. Every circle with b=t has this pole in its numerator.
            offset = f.mul(f.bar[pole], pole) ^ f.real
            repeated = (offset == evaluate(h0, pole)) if s == 1 else (offset == 0)
            accumulate(pole, pole, f.real, repeated)
        t, v = t[v != 0], v[v != 0]
        r = f.mul(evaluate(h0, t), f.inv(v))
        rp = f.mul(evaluate([h0[1], 0, h0[3]], t)^r, f.inv(v))
        if s == 2:
            r = f.sqrt(r)
        tr, alpha = f.mul(t, r), r^f.bar[t]
        for ti, ri, slope in zip(t[alpha == 0], r[alpha == 0], rp[alpha == 0]):
            d = f.mul(ti, ri)^f.mul(centers, ri)^f.mul(f.bar[centers], ti)
            accumulate(ti, centers, d, tangent(ti, centers, ri, slope))
        t, r, rp, tr, alpha = (v[alpha != 0, None] for v in (t, r, rp, tr, alpha))
        if not len(t):
            continue
        b = f.mul(f.mul(f.delta, tr^f.bar[tr]) ^ f.real, f.inv(alpha))
        d = tr ^ f.mul(b, r) ^ f.mul(f.bar[b], t)
        accumulate(t, b, d, tangent(t, b, r, rp))
    centers = centers[f.key == centers]  # Test one center per F_4 orbit.
    kept = []
    all_count = 0
    for b in centers:
        good = np.flatnonzero(totals[b*q:(b+1)*q] == degree)
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
        for _ in range(1, f.m//length):
            for _ in range(length):
                z = f.fourth[z]
            least = np.minimum(least, z)
        kept.extend((int(b)*q+good[least == d]).tolist())
    if all_count != f.split or len(kept) != f.rows:
        raise ArithmeticError("incorrect smooth circle census")
    return np.asarray(kept, dtype="<u4").tobytes()


class Equations:
    def __init__(self, f):
        self.f = f
        self.k = fq_default_ctx(modulus=binary_polynomial(f.modulus, fmpz_mod_poly_ctx(2)), var="w")
        self.ring = fq_default_poly_ctx(self.k)
        self.t = self.ring.gen()
        w = scalar(f.omega, self.k)**f.stretch
        self.h0 = self.ring([1, w+1, 1, w, w])
        self.h1 = self.t**2+self.t
        points = np.arange(1, f.size, dtype=np.int32)
        norms = f.index[f.mul(points, f.bar[points])]
        order = np.argsort(norms, kind="stable")
        self.radii = np.split(points[order], np.cumsum(np.bincount(norms))[:-1])
        self.element = lru_cache(maxsize=8192)(lambda c: scalar(c, self.k))

    def row(self, code):
        f = self.f
        b, i = divmod(code, f.q)
        d, bb = int(f.real[i]), int(f.bar[b])
        radius = f.index[d ^ int(f.mul(b, bb))]
        if radius == 0:
            raise ValueError("singular norm circle")
        s = f.stretch
        p = (self.t+self.element(b))**s*self.h0+(self.element(bb)*self.t+self.element(d))**s*self.h1
        roots = p.roots()
        if sum(mult for _, mult in roots) != 4+s:
            raise ArithmeticError("a purported split numerator has a nonlinear factor")
        coeff = Counter(f.var[self.radii[radius] ^ bb].tolist())
        scale = f.q//s
        coeff[int(f.var[0])] += scale
        coeff[int(f.var[1])] += scale
        for root, mult in roots:
            coeff[int(f.var[f.bar[bits(root)]])] -= scale*mult
        return sorted((int(t), w) for t, w in coeff.items() if w)


def verify_rank(f):
    from phase2_minpoly import half_gcd_minpoly, read_moments, write_u960

    cert = json.loads((DATA / "degree-1229-q1024-quaternary-rank.json").read_text())
    raw = gzip.decompress((DATA / "degree-1229-q1024-quaternary-moments.bin.gz").read_bytes())
    n, seq = read_moments(raw)
    if (cert["model"] != 21149 or cert["q"] != f.q or cert["circle_rows"] != f.rows
            or n != cert["dimension"] or n != len(f.labels) or len(seq) != cert["moment_count"]
            or sha256(raw).hexdigest() != cert["moments_sha256"]):
        raise ArithmeticError("rank certificate and archived matrix dimensions or moments disagree")
    p = half_gcd_minpoly(seq, COFACTOR, certify_rank=True)
    if len(p)-1 != n or p[0] != int(cert["minimal_recurrence_constant_mod_C"]):
        raise ArithmeticError("incorrect full-degree recurrence")
    scale = -pow(p[0], -1, COFACTOR)
    digest = sha256(struct.pack("<I", n))
    for c in p[1:]:
        digest.update(write_u960(c*scale % COFACTOR))
    if digest.hexdigest() != cert["phase3_coefficients_sha256"]:
        raise ArithmeticError("incorrect normalized recurrence coefficients")
    print(f"The {len(seq):,} archived moments certify augmented rank {n:,} modulo the full cofactor.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", type=int, choices=PARAMETERS, default=512, help="circle field size (default 512)")
    parser.add_argument("--rebuild", action="store_true", help="repeat the incidence census of all nonsingular norm circles")
    parser.add_argument("--matrix", type=Path, help="write the checked matrix in the Wiedemann solver's binary format")
    parser.add_argument("--row", type=int, metavar="INDEX", help="export a zero-based archived row")
    parser.add_argument("--check-logs", action="store_true", help="check the published vector against every circle modulo C")
    parser.add_argument("--solution", type=Path, help="compare a phase-three binary solution with the published table")
    parser.add_argument("--rank", action="store_true", help="verify the archived q=1024 full-rank recurrence")
    args = parser.parse_args()
    if args.rank and args.q != 1024:
        parser.error("--rank requires --q 1024")
    f = Constants(args.q)
    data = gzip.decompress((DATA/f"degree-1229-q{f.q}-quaternary-pencils.bin.gz").read_bytes())
    if len(data) != f.rows*4 or sha256(data).hexdigest() != f.digest:
        raise ArithmeticError("incorrect circle parameter archive")
    if args.rank:
        verify_rank(f)
    if args.rebuild:
        if census(f) != data:
            raise ArithmeticError("the reconstructed archive differs from the published identifiers")
    codes = np.frombuffer(data, dtype="<u4")
    if args.matrix or args.row is not None or args.check_logs:
        equations = Equations(f)
    if args.check_logs or args.solution:
        filename = DATA/f"degree-1229-q{f.q}-quaternary-logs.csv.gz"
        if not filename.exists():
            parser.error(f"the q={f.q} exponent table has not been published")
        with gzip.open(filename, "rt", newline="") as stream:
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
        entry = struct.Struct("<Hi" if len(f.labels) <= 1 << 16 else "<Ii")
        with args.matrix.open("wb") as stream:
            stream.write(struct.pack("<II", len(f.labels), len(codes)))
            stream.write(f.labels.astype("<u4").tobytes())
            for code in codes:
                row = equations.row(int(code))
                stream.write(struct.pack("<H", len(row)))
                stream.write(b"".join(entry.pack(t, w) for t, w in row))
        if f.q == 1024:
            digest = sha256()
            with args.matrix.open("rb") as stream:
                for block in iter(lambda: stream.read(1 << 20), b""):
                    digest.update(block)
            cert = json.loads((DATA / "degree-1229-q1024-quaternary-rank.json").read_text())
            if digest.hexdigest() != cert["matrix_sha256"]:
                raise ArithmeticError("the reconstructed matrix differs from the rank certificate")
    if args.row is not None:
        if not 0 <= args.row < len(codes):
            parser.error("row index outside the archive")
        code = int(codes[args.row])
        b, i = divmod(code, f.q)
        print(json.dumps({"b":hex(b), "d":hex(int(f.real[i])),
                          "coefficients":[[hex(int(f.labels[t])), w] for t,w in equations.row(code)]}))
    else:
        print(f"Verified {f.rows:,} archived orbit representatives on {len(f.labels):,} labels in model 21149.")


if __name__ == "__main__":
    main()
