"""Recover projected factor-base logarithms from the two degree-2047 circle matrices."""

import argparse
import gzip
import os
import struct
import time
from pathlib import Path

import numpy as np

from check_2047_ore_circles import COFACTOR, FIELD_DEGREES, GROUP_ORDER
from phase2_minpoly import half_gcd_minpoly


def words(values):
    raw = b"".join(int(v).to_bytes(256, "little") for v in values)
    return np.frombuffer(raw, dtype="<u4").reshape(-1, 64)


def integer(row):
    return int.from_bytes(row.astype("<u4", copy=False).tobytes(), "little")


def vectors(q, n):
    generator = np.random.PCG64(2047+q)
    return [(1+generator.random_raw(n) % bound).astype(np.uint32)
            for bound in (65535, 32767, 32767)]


class Matrix:
    """Each warp evaluates one signed CSR row modulo 2^2047-1."""

    def __init__(self, ptr, entries, diagonal, u, start, count, coefficients=None):
        import cupy as cp
        n = self.n = len(ptr)-1
        row_l1 = np.add.reduceat(abs((entries >> 16).astype(np.int16).astype(np.int64)), ptr[:-1])
        # Leave room for the injected coefficient and the signed carry from the preceding limb.
        if (int(max(row_l1))*int(max(diagonal))*(1 << 32) + (2 << 32) >= 1 << 63
                or n*int(max(u))*((1 << 32)-1) + (1 << 32) >= 1 << 63):
            raise ValueError("signed accumulation would exceed the GPU word size")
        self.ptr, self.entries, self.diagonal, self.u = map(cp.asarray, (ptr, entries, diagonal, u))
        self.value = cp.asarray(start)
        self.next_value = cp.empty_like(self.value)
        self.coefficients = self.value if coefficients is None else cp.asarray(coefficients)
        self.blocks = (n+127)//128
        self.partial = cp.empty((self.blocks, 64), dtype=cp.uint64)
        self.seq = cp.empty((count, 64), dtype=cp.uint32)
        code = Path(__file__).with_name("ore_2047_mersenne.cu").read_text()
        module = cp.RawModule(code=code, options=("--std=c++17",))
        self.multiply_row = module.get_function("spmv")
        self.project_rows = module.get_function("partial")
        self.finish_projection = module.get_function("finish")

    def multiply(self, add_index=-1):
        self.multiply_row(((self.n+3)//4,), (128,),
                          (self.ptr, self.entries, self.diagonal, self.value, self.next_value,
                           np.int32(self.n), self.coefficients, np.int32(add_index)))
        self.value, self.next_value = self.next_value, self.value

    def project(self, index):
        self.project_rows((self.blocks,), (256,), (self.value, self.u, self.partial, np.int32(self.n)))
        self.finish_projection((1,), (64,), (self.partial, self.seq, np.int32(self.blocks), np.int32(index)))


def selftest():
    """Check every limb of signed products, end-around carries and Horner additions in Python."""
    gen = np.random.default_rng(77)
    n = 128
    ptr = np.arange(0, n*n+1, n, dtype=np.uint32)
    c = gen.integers(-150, 151, (n, n), dtype=np.int32)
    c[:, 0] = 0
    c[:3] = 0
    c[1, 1], c[2, 2] = -1, 1
    entries = np.tile(np.arange(n, dtype=np.uint32), n) | (c.ravel().astype(np.uint32) << 16)
    diagonal, u, _ = vectors(19, n)
    diagonal[:3] = 1
    def random_value():
        return int.from_bytes(gen.bytes(256), "little") % GROUP_ORDER
    v = [random_value() for _ in range(n)]
    v[:3] = [0, 1, GROUP_ORDER-1]
    add = [random_value() for _ in range(7)]
    matrix = Matrix(ptr, entries, diagonal, u, words(v), 7, words(add))
    for k in range(7):
        matrix.multiply(k)
        matrix.project(k)
        v = [int(d)*sum(int(a)*b for a, b in zip(row, v)) % GROUP_ORDER for d, row in zip(diagonal, c)]
        v[-1] = (v[-1]+add[k]) % GROUP_ORDER
        if ([integer(row) % GROUP_ORDER for row in matrix.value.get()] != v
                or integer(matrix.seq[k].get()) % GROUP_ORDER != sum(int(a)*b for a, b in zip(u, v)) % GROUP_ORDER):
            raise ArithmeticError("GPU self-test failed")


def save_checkpoint(path, **data):
    tmp = path.with_suffix(".new")
    with tmp.open("wb") as out:
        np.savez(out, **data)
    os.replace(tmp, path)


def gpu_phase(q, folder, chunk, recover, output):
    selftest()
    ptr = np.load(folder / f"q{q}-ptr.npy")
    entries = np.load(folder / f"q{q}-entries.npy")
    masks = np.load(folder / f"q{q}-masks.npy")
    n = len(masks)
    diagonal, u, b = vectors(q, n)
    total = n if recover else 2*n
    if recover:
        coeffs = np.load(folder / f"poly{q}.npy")
        if coeffs.shape != (n+1, 64) or integer(coeffs[-1]) != 1:
            raise ValueError("expected a complete monic matrix polynomial")
        matrix = Matrix(ptr, entries, diagonal, u, np.zeros((n,64), np.uint32), 0, coeffs)
        path = folder / f"solution{q}.npz"
    else:
        matrix = Matrix(ptr, entries, diagonal, u, words(b), total)
        path = folder / f"wide{q}-{total}.npz"
    start = 0
    if path.exists():
        with np.load(path) as saved:
            matrix.value.set(saved["state"])
            if recover:
                start = int(saved["done"])
            else:
                start = len(saved["moments"])
                matrix.seq[:start].set(saved["moments"])
    if not 0 <= start <= total:
        raise ValueError("invalid checkpoint position")
    began = time.monotonic()
    for lo in range(start, total, chunk):
        hi = min(total, lo+chunk)
        for k in range(lo, hi):
            if recover:
                matrix.multiply(n-k)
            else:
                matrix.multiply()
                matrix.project(k)
        if recover:
            save_checkpoint(path, state=matrix.value.get(), done=hi)
        else:
            save_checkpoint(path, state=matrix.value.get(), moments=matrix.seq[:hi].get())
        print(f"q={q} {hi}/{total}, {(time.monotonic()-began)/(hi-start)*1000:.1f} ms/step", flush=True)
    if recover:
        scale = -int(diagonal[-1])*pow(integer(coeffs[0]), -1, COFACTOR) % COFACTOR
        logs = [integer(row)*scale % COFACTOR for row in matrix.value.get()]
        if masks[0] != 2 or logs[0] != 1:
            raise ArithmeticError("the recovered vector does not have the required anchor")
        archive = output or folder / f"degree-2047-q{q}-projected.bin.gz"
        with archive.open("wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as sink:
            sink.write(struct.pack("<4sII", b"G2O1", q, n))
            for mask, log in sorted(zip(map(int, masks), logs)):
                sink.write(mask.to_bytes(4, "little")+log.to_bytes(228, "little"))
        print(f"Wrote {n} projected logarithms to {archive}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["moments", "polynomial", "recover"])
    parser.add_argument("q", type=int, choices=FIELD_DEGREES)
    parser.add_argument("--work-dir", type=Path, default=Path(".lake/ore-2047"))
    parser.add_argument("--chunk", type=int, default=512)
    parser.add_argument("--output", type=Path, help="destination of the recovered logarithms")
    args = parser.parse_args()
    if args.chunk < 1 or (args.output and args.phase != "recover"):
        parser.error("use a positive chunk size and specify an output only for recover")
    q, folder = args.q, args.work_dir
    if args.phase == "polynomial":
        n = len(np.load(folder / f"q{q}-masks.npy"))
        with np.load(folder / f"wide{q}-{2*n}.npz") as checkpoint:
            moments = checkpoint["moments"]
        if moments.shape != (2*n, 64):
            raise ValueError("incomplete moment sequence")
        coeffs = half_gcd_minpoly([integer(row) % COFACTOR for row in moments], COFACTOR, certify_rank=True)
        np.save(folder / f"poly{q}.npy", words(coeffs))
    else:
        gpu_phase(q, folder, args.chunk, args.phase == "recover", args.output)


if __name__ == "__main__":
    main()
