"""Find a real elliptic pencil by interpolating a determinant over F_1024."""

import argparse
import json
import sys

import numpy as np

from check_1229_elliptic_real_pencils import MODULUS, RING, T, homogeneous_powers, scalar, verify_row


def bits(c):
    return sum(int(v) << i for i, v in enumerate(c.to_list()))


def field_tables():
    elements = np.arange(1024, dtype=np.uint16)
    modulus = sum(b << i for i, b in enumerate(MODULUS))
    powers = [elements]
    for _ in range(9):
        shifted = powers[-1] << 1
        powers.append(shifted ^ ((shifted >> 10)*modulus))
    products = np.bitwise_xor.reduce([((elements >> j) & 1)[:, None]*p for j, p in enumerate(powers)])
    inverses = np.array([0, *(bits(scalar(i)**-1) for i in range(1, 1024))], dtype=np.uint16)
    return products, inverses


def determinants(matrices, mul, inv):
    """Eliminate each sample matrix independently, retaining zero determinants."""
    a = matrices.copy()
    samples, n, _ = a.shape
    indices = np.arange(samples)
    det = np.ones(samples, dtype=np.uint16)
    for j in range(n):
        pivot = j + np.argmax(a[:, j:, j] != 0, axis=1)
        a[:, j, :], a[indices, pivot, :] = a[indices, pivot, :].copy(), a[:, j, :].copy()
        column = a[:, j, j]
        det = mul[det, column]
        ratios = mul[a[:, j+1:, j], inv[column, None]]
        a[:, j+1:, j+1:] ^= mul[ratios[:, :, None], a[:, None, j, j+1:]]
    return det


def solve(matrix, mul, inv):
    """Solve the full-column-rank system given by an augmented square matrix."""
    a = matrix.copy()
    for j in range(len(a)-1):
        rows = np.flatnonzero(a[j:, j])
        if not len(rows):
            return None
        pivot = j + rows[0]
        a[[j, pivot]] = a[[pivot, j]]
        a[j] = mul[inv[a[j, j]], a[j]]
        column = a[:, j].copy()
        column[j] = 0
        a ^= mul[column[:, None], a[j]]
    return None if a[-1, -1] else a[:-1, -1]


def lagrange_values(samples, mul, inv):
    elements = np.arange(1024, dtype=np.uint16)
    values = np.ones((1024, samples), dtype=np.uint16)
    for i in range(samples):
        for j in range(samples):
            if i != j:
                values[:, i] = mul[values[:, i], mul[elements ^ j, inv[i ^ j]]]
    return values


def search(mask, seed, lines):
    binary = RING([(mask >> i) & 1 for i in range(mask.bit_length())])
    p = min((f for f, _ in binary.factor()[1]), key=lambda f: tuple(map(bits, f.coeffs())))
    t = p.degree()
    m = t-1
    powers = homogeneous_powers(m)
    # B[i,j] represents H0^i H1^(m-i) T^j modulo the designated factor.
    B = np.zeros((t, t, t), dtype=np.uint16)
    for i, power in enumerate(powers):
        residue = power % p
        for j in range(t):
            B[i, j, :residue.length()] = list(map(bits, residue.coeffs()))
            residue = residue*T % p
    symmetric = B ^ B.swapaxes(0, 1)
    mul, inv = field_tables()
    samples = np.arange(t+2, dtype=np.uint16)
    interpolation = lagrange_values(t+2, mul, inv)
    rng = np.random.default_rng(seed)

    def matrices(parameters, columns, rhs):
        u = parameters[:, None]
        mats = np.empty((len(u), t, t), dtype=np.uint16)
        mats[:, :, :-1] = (columns[None, :m] ^ mul[u[:, :, None], symmetric[None, 0, :m]]).swapaxes(1, 2)
        mats[:, :, -1] = rhs ^ mul[u, columns[0]] ^ mul[mul[u, u], B[0, 0]]
        return mats

    for line in range(lines):
        g = rng.integers(0, 1024, size=t, dtype=np.uint16)
        g[0], g[-1] = 0, 1
        columns = np.bitwise_xor.reduce(mul[g[:, None, None], symmetric])
        pairs = mul[g[:, None], g[None, :]]
        rhs = np.bitwise_xor.reduce(mul[pairs[:, :, None], B].reshape(t*t, t))
        sample_values = determinants(matrices(samples, columns, rhs), mul, inv)
        if not np.any(sample_values):
            continue
        values = np.bitwise_xor.reduce(mul[interpolation, sample_values], axis=1)
        roots = np.flatnonzero(values == 0).astype(np.uint16)
        for u, matrix in zip(roots, matrices(roots, columns, rhs)):
            h = solve(matrix, mul, inv)
            if h is None:
                continue
            g[0] = u
            gs, hs = list(map(int, g)), list(map(int, h))
            G, H = (RING([scalar(c) for c in coeffs]) for coeffs in (gs, hs))
            if not G.gcd(H).is_one():
                continue
            def homogeneous(f):
                return sum((c*v for c, v in zip(f.coeffs(), powers)), RING.zero())
            cofactor, remainder = divmod(homogeneous(G)*(G+H) + homogeneous(H)*G, p)
            if not remainder.is_zero():
                raise ArithmeticError("the interpolated equation misses its target")
            if cofactor.is_zero() or any(f.degree()//(1 if f.degree()%2 else 2) > m
                                         for f, _ in cofactor.factor()[1]):
                continue
            verify_row((mask, gs, hs))
            print(f"Found on line {line + 1}.", file=sys.stderr)
            return [hex(mask), gs, hs]
    return None


def main():
    from check_factor_base import irreducible, polynomial

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mask", type=lambda s: int(s, 0))
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--lines", type=int, default=4000)
    args = parser.parse_args()
    if args.mask.bit_length()-1 not in (130, 150) or not irreducible(polynomial(args.mask)):
        parser.error("choose an irreducible degree-130 or degree-150 mask")
    if args.lines < 1 or args.seed < 0:
        parser.error("choose a positive line count and nonnegative seed")
    row = search(args.mask, args.seed, args.lines)
    if row is None:
        sys.exit("No smooth pencil on the sampled lines.")
    print(json.dumps(row))


if __name__ == "__main__":
    main()
