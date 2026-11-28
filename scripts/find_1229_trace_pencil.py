"""Find a degree-(d-1) trace-zero pencil through a degree-d relative factor."""

import argparse
import json
import random

import numpy as np

from check_1229_translated_circles import Constants
from find_1229_hermitian_descent import nullspace


def interpolation_bases(mask):
    """Return the minimal polynomials of gamma and beta, and the powers of alpha in the beta basis."""
    from check_1229_hermitian_descent import H0, H1, K, Q, T, relative_factor

    target = relative_factor(mask)
    d = target.degree()
    phi = K([c**Q for c in target.coeffs()])
    beta = H0*H1.inverse_mod(target) % target
    powers = [K.one()]
    for _ in range(d):
        powers.append(beta*powers[-1] % target)

    def in_beta_basis(value):
        columns = powers[:d] + [value]
        kernel = nullspace([[p[i] for p in columns] for i in range(d)], d+1)
        if len(kernel) != 1 or not kernel[0][-1].is_one():
            raise ValueError("the rational image does not generate the target residue field")
        return K(kernel[0][:-1])

    psi = T**d + in_beta_basis(powers[d])
    if phi == psi or not psi.compose_mod(beta, target).is_zero():
        raise ValueError("this interpolation requires two distinct evaluation polynomials")
    return target, phi, psi, [in_beta_basis(T**i) for i in range(d)]


def interpolation_matrix(phi, psi, beta_basis, value):
    """A kernel vector g makes the two prescribed remainders for h agree."""
    from check_1229_hermitian_descent import K, Q, T

    first = value
    second = sum((value[i]**Q*p for i, p in enumerate(beta_basis)), K.zero())
    columns = []
    for _ in beta_basis:
        columns.append(first+second)
        first = T*first % phi
        second = T*second % psi
    return [[p[i] for p in columns] for i in range(len(columns))]


def determinants(field, matrices):
    """Evaluate a sample grid of determinants by independent row reduction."""
    work = matrices.copy()
    batch, degree, _ = work.shape
    ids = np.arange(batch)
    values = np.ones(batch, dtype=np.int32)
    for i in range(degree):
        pivots = i + (work[:, i:, i] != 0).argmax(axis=1)
        changed = pivots != i
        if changed.any():
            s, p = ids[changed], pivots[changed]
            work[s, i, :], work[s, p, :] = work[s, p, :].copy(), work[s, i, :].copy()
        diagonal = work[:, i, i]
        values = field.multiply(values, diagonal)
        if i+1 < degree:
            inv = field.power[-field.log[diagonal]]
            scales = field.multiply(work[:, i+1:, i], inv[:, None])
            work[:, i+1:, i+1:] ^= field.multiply(scales[:, :, None], work[:, None, i, i+1:])
    return values


def interpolation_weights(field, n, real):
    nodes = real[:n]
    weights = []
    for i in range(n):
        numerators = np.ones(len(real), dtype=np.int32)
        denominator = 1
        for j in range(n):
            if j != i:
                numerators = field.multiply(numerators, real ^ nodes[j])
                denominator = field.multiply(denominator, nodes[i] ^ nodes[j])
        weights.append(field.multiply(numerators, field.power[-field.log[denominator]]))
    return np.array(weights)


def determinant_zeros(field, matrices, real, weights, real_index, real_products, first_component):
    """Interpolate det(M0+s M1+l I) and find every zero over the real scalar field."""
    a, b = matrices
    d = len(a)
    nodes = real[:d+1]
    line = a ^ field.multiply(b[None, :, :], nodes[:, None, None])
    grid = line[:, None, :, :] ^ field.multiply(np.eye(d, dtype=np.int32), nodes[None, :, None, None])
    samples = determinants(field, grid.reshape(-1, d, d)).reshape(d+1, d+1)
    by_s = np.bitwise_xor.reduce(field.multiply(weights[:, :, None], samples[:, None, :]), axis=0)
    # Screen all pairs in one F_q coordinate, then check the surviving pairs in F_(q^2).
    first = np.zeros((len(real), len(real)), dtype=np.uint16)
    for j in range(d+1):
        first ^= real_products[first_component[by_s[:, j]][:, None], real_index[weights[j]][None, :]]
    s, l = np.nonzero(first == 0)
    full = np.zeros(len(s), dtype=np.int32)
    for j in range(d+1):
        full ^= field.multiply(by_s[s, j], weights[j, l])
    return zip(real[s[full == 0]], real[l[full == 0]])


def find(mask, start, count):
    from check_1229_hermitian_descent import H0, H1, K, Q, bits, element

    target, phi, psi, beta_basis = interpolation_bases(mask)
    d = target.degree()
    if d < 2 or d >= Q:
        raise ValueError("the degree must lie between 2 and q-1")
    field = Constants()
    real = np.flatnonzero(field.bar == field.elements).astype(np.int32)
    real_index = np.zeros(Q**2, dtype=np.int32)
    real_index[real] = np.arange(Q)
    real_products = real_index[field.multiply(real[:, None], real[None, :])].astype(np.uint16)
    c = element(2)/(element(2)+element(2)**Q)
    first_component = real_index[field.elements ^ field.multiply(bits(c), field.bar ^ field.elements)]
    weights = interpolation_weights(field, d+1, real)
    powers = [H0**i*H1**(d-1-i) for i in range(d)]

    def homogeneous(p):
        return sum((a*v for a, v in zip(p.coeffs(), powers)), K.zero())

    def conjugate(p):
        return K([a**Q for a in p.coeffs()])

    for plane in range(start, start+count):
        rng = random.Random((mask << 44)+plane)
        directions = [K([element(rng.randrange(Q**2)) for _ in range(d)]) for _ in range(2)]
        matrices = [np.array([[bits(a) for a in row] for row in interpolation_matrix(phi, psi, beta_basis, v)],
                             dtype=np.int32) for v in directions]
        for s, l in determinant_zeros(field, matrices, real, weights, real_index, real_products, first_component):
            value = directions[0]+element(int(s))*directions[1]+element(int(l))*c
            kernel = nullspace(interpolation_matrix(phi, psi, beta_basis, value), d)
            if not kernel:
                raise ArithmeticError("the interpolated determinant gave a nonsingular matrix")
            for vector in kernel:
                g = K(vector)
                h = value*g % phi
                if max(g.degree(), h.degree()) != d-1 or g.gcd(h).degree() != 0:
                    continue
                residual, rem = divmod(homogeneous(g)*conjugate(h)+homogeneous(h)*conjugate(g), target)
                if not rem.is_zero():
                    raise ArithmeticError("the reconstructed pencil misses its target")
                if residual.is_zero():
                    continue
                degrees = sorted(p.degree() for p, e in residual.factor()[1] for _ in range(e))
                if all(k < d for k in degrees):
                    return {"mask_hex": hex(mask), "relative_factor": [bits(a) for a in target.coeffs()],
                            "g": [bits(a) for a in g.coeffs()], "h": [bits(a) for a in h.coeffs()],
                            "plane": plane, "s": int(s), "lambda": int(l), "residual_degrees": degrees}
    return None


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mask", type=lambda p: int(p, 0), help="binary irreducible mask")
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--count", type=int, default=1)
    args = parser.parse_args()
    if args.start < 0 or args.count < 1:
        parser.error("use a nonnegative start and positive count")
    row = find(args.mask, args.start, args.count)
    if row is not None:
        print(json.dumps(row))
