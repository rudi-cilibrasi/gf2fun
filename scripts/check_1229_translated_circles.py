"""Check translated norm circles in degree 1229 and certify a minor modulo the full group order."""

import argparse
import hashlib
import json
from collections import Counter
from math import gcd

import numpy as np
from flint import fmpz_mat

from check_1229_frobenius_models import TABLE
from check_degree_1229 import GROUP
from check_factor_base import polynomial


Q = 1024
SIZE = Q**2
COLUMNS = "center,norm_radius,root0,root1,root2,root3,root4,root5"
MINORS = {
    1536: ("955ebfc42c663f516eaaa755131db798e2b778ef920d2550e6db0ef956da7c80", 2739),
    4096: ("b968e9e33a742735ce29a57dc8a45ad375b2059b66967ad5f9a98bab79aea436", 10296),
}


class Constants:
    """Polynomial-basis elements of F_(2^20), with the low bit the constant coefficient."""

    def __init__(self):
        powers = []
        x = 1
        for _ in range(SIZE - 1):
            powers.append(x)
            x <<= 1
            if x & SIZE:
                x ^= SIZE | 9
        self.power = np.array(powers, dtype=np.int32)
        if x != 1 or np.unique(self.power).size != SIZE - 1:
            raise ValueError("X does not generate the chosen constant field")
        self.log = np.zeros(SIZE, dtype=np.int32)
        self.log[self.power] = np.arange(SIZE - 1)
        self.elements = np.arange(SIZE, dtype=np.int32)
        self.square = np.r_[np.int32(0), self.power[(2 * self.log[1:]) % (SIZE - 1)]]
        self.bar = np.r_[np.int32(0), self.power[(Q * self.log[1:]) % (SIZE - 1)]]
        self.rep = self.elements.copy()
        self.degree = np.full(SIZE, 20, dtype=np.int32)
        conjugate = self.elements
        for i in range(1, 20):
            conjugate = self.square[conjugate]
            self.rep = np.minimum(self.rep, conjugate)
            if 20 % i == 0:
                self.degree[(conjugate == self.elements) & (self.degree == 20)] = i
        self.torus_exponents = (Q - 1) * np.arange(Q + 1)

    def multiply(self, a, b):
        product = self.power[(self.log[a] + self.log[b]) % (SIZE - 1)]
        return np.where((a != 0) & (b != 0), product, 0)

    def h0_h1(self, a):
        square = self.square[a]
        cube = self.multiply(a, square)
        return self.multiply(cube, square) ^ square ^ 1, cube ^ a

    def circle_points(self, center, rho):
        radius_log = int(self.log[rho])
        if rho == 0 or radius_log % (Q + 1):
            raise ValueError("the norm radius must be a nonzero base-field element")
        # sqrt(rho) = rho^(q/2).
        shift = radius_log * (Q // 2) % (SIZE - 1)
        return center ^ self.power[(shift + self.torus_exponents) % (SIZE - 1)]

    def norm_polynomials(self, points):
        """Compute the binary masks of the full constant-field norms of T + c."""
        coefficients = np.ones((len(points), 1), dtype=np.int32)
        conjugates = points
        for _ in range(20):
            result = np.zeros((len(points), coefficients.shape[1] + 1), dtype=np.int32)
            result[:, 1:] = coefficients
            result[:, :-1] ^= self.multiply(coefficients, conjugates[:, None])
            coefficients = result
            conjugates = self.square[conjugates]
        if np.any(coefficients > 1):
            raise ArithmeticError("a norm has nonbinary coefficients")
        return coefficients @ (1 << np.arange(21, dtype=np.int32))


def load_rows(path):
    with open(path, encoding="ascii") as source:
        if source.readline().strip() != COLUMNS:
            raise ValueError("incorrect circle CSV columns")
        rows = np.loadtxt(source, delimiter=",", dtype=np.int32)
    if rows.shape != (92910, 8) or np.any((rows < 0) | (rows >= SIZE)):
        raise ValueError("incorrect circle count or field representation")
    return rows


def audit_centers(field, rows):
    """For these centers scan every possible sextic root directly, including the two poles."""
    a = field.elements
    h0, h1 = field.h0_h1(a)
    inv = field.power[(-field.log[h1]) % (SIZE - 1)]
    t = field.multiply(h0, inv)
    regular = h1 != 0
    radii = field.power[(Q + 1) * np.arange(Q - 1)]
    for center in (0, 1, 2, 3, 27, 166769):
        if field.rep[center] != center:
            raise ValueError("the selected center is not canonical")
        rho = field.multiply(t ^ center, a ^ field.bar[center])
        valid = regular & (rho != 0) & (field.bar[rho] == rho)
        counts = np.bincount(rho[valid], minlength=SIZE)
        if center in (0, 1):
            counts[radii] += 1
        expected = {}
        for r in np.flatnonzero(counts[radii] == 6):
            degree = int(field.degree[center])
            if any(int(r) * (1 << j) % (Q - 1) < r for j in range(degree, 20, degree)):
                continue
            radius = int(radii[r])
            roots = a[valid & (rho == radius)].tolist()
            if center in (0, 1):
                roots.append(center)
            expected[radius] = sorted(roots)
        actual = {int(row[1]): row[2:].tolist() for row in rows[rows[:, 0] == center]}
        if actual != expected:
            raise ArithmeticError(f"direct enumeration differs at center {center}")


def check_field_identities(field, rows):
    model = next(m for m in json.loads(TABLE.read_text()) if m["q"] == Q)
    modulus = polynomial(int(model["modulus_hex"], 16))
    x = polynomial(2)
    y = x.pow_mod(Q, modulus)
    h1 = y**3 + y
    if (x * h1 + y**5 + y**2 + 1) % modulus:
        raise ArithmeticError("the Frobenius relation failed in degree 1229")

    def norm_product(points):
        value = polynomial(1)
        for mask, count in Counter(field.norm_polynomials(points).tolist()).items():
            value = value * polynomial(mask).pow_mod(count, modulus) % modulus
        return value

    for i in (0, 23, 192, 938, 21973, 70001, len(rows) - 1):
        center, rho = rows[i, :2]
        left = norm_product(field.circle_points(center, rho)) * h1.pow_mod(20, modulus)
        right = norm_product(rows[i, 2:]).pow_mod(Q, modulus)
        if left % modulus != right:
            raise ArithmeticError(f"the norm identity failed in degree 1229 at row {i}")


def pivot_columns(field, dimension):
    full = field.elements[(field.rep == field.elements) & (field.degree == 20)]
    if len(full) != 52377:
        raise ArithmeticError("wrong number of degree-20 orbits")
    # The step is coprime to the orbit count. Omit the orbit satisfying h0(c) = c^q h1(c).
    ordered = full[(8191 * np.arange(len(full), dtype=np.int64)) % len(full)]
    h0, h1 = field.h0_h1(ordered)
    keep = h0 != field.multiply(h1, field.bar[ordered])
    if ordered[~keep].tolist() != [166769]:
        raise ArithmeticError("incorrect exceptional degree-20 orbit")
    return ordered[keep][:dimension]


def circle_minor(field, rows, dimension):
    columns = pivot_columns(field, dimension)
    index = np.full(SIZE, -1, dtype=np.int32)
    index[columns] = np.arange(dimension)
    index = index[field.rep]
    matrix = np.zeros((dimension, dimension), dtype=np.uint8)
    used = 0
    for i in range(len(rows)):
        row = rows[(65537 * i) % len(rows)]
        # On these columns the right-hand side and the fixed h1 contribute zero.
        if np.any(index[row[2:]] >= 0):
            continue
        hits = index[field.circle_points(*row[:2])]
        counts = np.bincount(hits[hits >= 0], minlength=dimension)
        if not np.any(counts):
            continue
        if counts.max() > 20:
            raise ArithmeticError("a circle meets an orbit more than 20 times")
        matrix[used] = counts
        used += 1
        if used == dimension:
            break
    if used != dimension:
        raise ArithmeticError("too few eligible circle rows")
    if hashlib.sha256(matrix.tobytes()).hexdigest() != MINORS[dimension][0]:
        raise ArithmeticError("the reconstructed minor differs from the published matrix")
    return matrix


def check_minor(field, rows, dimension):
    matrix = circle_minor(field, rows, dimension)
    determinant = int(fmpz_mat(matrix.tolist()).det())
    if abs(determinant).bit_length() != MINORS[dimension][1] or gcd(determinant, GROUP) != 1:
        raise ArithmeticError("the integer determinant certificate failed")
    print(f"Verified {dimension} eliminable columns. The integer determinant has "
          f"{abs(determinant).bit_length()} bits and gcd 1 with 2^1229-1.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("circles", help="CSV from enumerate_1229_translated_circles --csv")
    parser.add_argument("--minor", type=int, choices=(1536, 4096), help="verify this many eliminable columns")
    args = parser.parse_args()
    field = Constants()
    table = load_rows(args.circles)
    audit_centers(field, table)
    check_field_identities(field, table)
    print("Verified six complete center slices and seven norm identities in the degree-1229 field.")
    if args.minor:
        check_minor(field, table, args.minor)
