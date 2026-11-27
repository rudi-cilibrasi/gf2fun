"""Certify irreducibility at a prime degree by batched CUDA modular squaring.

Read one triple of ordered taps per input line. Two reduction folds suffice
when 2*c-2 < n. For a five-term binary polynomial with these endpoints both
zero and one are nonroots. At prime n, X^(2^n) = X modulo f then forces f to
be a single irreducible factor of degree n.
"""

import argparse
import ctypes
import os
import sys
from itertools import islice
from math import isqrt
from pathlib import Path
from random import Random


def cuda_packages():
    """Also support CUDA 12 pip wheels on Linux machines without a system toolkit."""
    if sys.platform == "linux" and not os.environ.get("CUDA_PATH"):
        for directory in sys.path:
            nvidia = Path(directory) / "nvidia"
            runtime = nvidia / "cuda_runtime"
            compiler = nvidia / "cuda_nvrtc" / "lib"
            if (runtime / "include" / "cuda_runtime.h").is_file() and compiler.is_dir():
                os.environ["CUDA_PATH"] = str(runtime)
                for pattern in ("libnvrtc-builtins.so*", "libnvrtc.so*"):
                    library = next(compiler.glob(pattern), None)
                    if library:
                        ctypes.CDLL(str(library), mode=ctypes.RTLD_GLOBAL)
                break
    import cupy
    import numpy
    return cupy, numpy


class Frobenius:
    def __init__(self):
        self.cp, self.np = cuda_packages()
        source = Path(__file__).with_name("low_tap_frobenius.cu").read_text()
        self.kernel = self.cp.RawKernel(source, "square_mod", options=("--std=c++14",))
        self.kernel.compile()

    def powers(self, n, taps, values, steps):
        cp, np = self.cp, self.np
        words = (n + 31) // 32
        stride = 4 * (words + 3)
        raw = b"".join(value.to_bytes(stride, "little") for value in values)
        source = cp.asarray(np.frombuffer(raw, dtype="<u4"))
        target = cp.zeros_like(source)
        arguments = (cp.asarray(taps, dtype=cp.int32), np.int32(n), np.int32(words))
        grid = ((words + 255) // 256, len(taps))
        block = (256,)
        cp.cuda.get_current_stream().synchronize()
        stream = cp.cuda.Stream(non_blocking=True)
        with stream:
            if steps >= 64:
                stream.begin_capture()
                for _ in range(32):
                    self.kernel(grid, block, (target, source, *arguments))
                    self.kernel(grid, block, (source, target, *arguments))
                graph = stream.end_capture()
                for _ in range(steps // 64):
                    graph.launch(stream)
            for _ in range(steps % 64):
                self.kernel(grid, block, (target, source, *arguments))
                source, target = target, source
        stream.synchronize()
        rows = source.get().reshape(-1, words + 3)
        return [int.from_bytes(row.tobytes(), "little") for row in rows]


def reference_square(value, n, taps):
    square = sum(((value >> i) & 1) << (2 * i) for i in range(value.bit_length()))
    modulus = (1 << n) + 1 + sum(1 << a for a in taps)
    while square.bit_length() > n:
        square ^= modulus << (square.bit_length() - 1 - n)
    return square


def self_test(gpu):
    random = Random(73)
    for n in (11, 16, 31, 32, 33, 61, 64, 65, 117, 131, 257, 1025):
        limit = (n + 1) // 2
        taps = [tuple(sorted(random.sample(range(1, limit + 1), 3))) for _ in range(5)]
        taps.append((1, 2, limit))
        initial = [random.randrange(1 << n) for _ in taps]
        for steps in (1, 2, 67):
            actual = gpu.powers(n, taps, initial, steps)
            for value, triple, residue in zip(initial, taps, actual):
                for _ in range(steps):
                    value = reference_square(value, n, triple)
                if value != residue:
                    raise ArithmeticError(f"incorrect residue at degree {n}, taps {triple}, steps {steps}")
    print("All 216 GPU residues agree with binary polynomial long division.")


def read_taps(n):
    for number, line in enumerate(sys.stdin, 1):
        if not line.strip():
            continue
        try:
            a, b, c = map(int, line.split())
        except ValueError as error:
            raise ValueError(f"expected three integers on input line {number}") from error
        if not 0 < a < b < c < n or 2 * c - 2 >= n:
            raise ValueError(f"taps on line {number} must satisfy 0 < a < b < c < n and 2c-2 < n")
        yield a, b, c


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", nargs="?", type=int)
    parser.add_argument("--batch-size", type=int, default=8)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test(Frobenius())
        return
    n = args.degree
    if n is None or not 5 <= n < 2**30 or any(n % i == 0 for i in range(2, isqrt(n) + 1)):
        parser.error("degree must be prime and between 5 and 2^30-1")
    if not 1 <= args.batch_size <= 65535:
        parser.error("batch size must be between 1 and 65535")
    gpu = Frobenius()
    source = read_taps(n)
    while rows := list(islice(source, args.batch_size)):
        powers = gpu.powers(n, rows, [2] * len(rows), n)
        for triple, result in zip(rows, powers):
            print(n, *triple, "irreducible" if result == 2 else "reducible", flush=True)


if __name__ == "__main__":
    main()
