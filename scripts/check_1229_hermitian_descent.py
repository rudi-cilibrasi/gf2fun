"""Factor certified Hermitian equations and take their binary norms in the degree-1229 model."""

import json
from collections import Counter
from functools import cache
from itertools import combinations

from flint import fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx

from check_1229_isogeny_logs import Q
from check_degree_1229 import COFACTOR
from check_factor_base import DATA, polynomial
from period_coordinate import mask_of


CERTIFICATES = DATA / "degree-1229-hermitian-descents.json"
F = fq_default_ctx(modulus=fmpz_mod_poly_ctx(2)([1, 0, 0, 1] + [0]*16 + [1]), var="z")
K = fq_default_poly_ctx(F)
T = K.gen()
H0, H1 = T**5 + T**2 + 1, T**3 + T


def element(mask):
    if not 0 <= mask < Q**2:
        raise ValueError("constant outside the polynomial basis of F_(2^20)")
    return F([mask >> i & 1 for i in range(mask.bit_length())])


def bits(c):
    return sum(int(b) << i for i, b in enumerate(c.to_list()))


def records():
    rows = json.loads(CERTIFICATES.read_text())
    result = {int(r["mask_hex"], 16): r for r in rows}
    if len(rows) != len(result):
        raise ValueError("repeated Hermitian target")
    return result


def matrix(values):
    a, b, c, u, v, w = values
    if any(d != d**Q for d in (a, b, c)):
        raise ValueError("non-Hermitian diagonal")
    return [[a, u, v], [u**Q, b, w], [v**Q, w**Q, c]]


def numerator(h):
    return sum((h[i][j] * (H0**i * H1**(2-i) * T**j) for i in range(3) for j in range(3)), K.zero())


@cache
def scalar_groups():
    z = F.gen()
    u = z**(Q-1)
    torus = tuple(u**i for i in range(Q+1))
    v = z**(Q+1)
    real = (F.zero(), *(v**i for i in range(Q-1)))
    if (len({bits(t) for t in torus}) != Q+1 or u**(Q+1) != F.one()
            or len({bits(t) for t in real}) != Q or v**(Q-1) != F.one()):
        raise ArithmeticError("incomplete scalar groups")
    return torus, real


def pencil(h):
    """Express the Hermitian form as a product of q+1 forms of degree at most two."""
    for i, j in combinations(range(3), 2):
        a, c, u = h[i][i], h[j][j], h[i][j]
        if not (a*c + u*u**Q).is_zero():
            break
    else:
        raise ValueError("missing nonsingular principal minor")
    f = K([row[i] for row in h])
    g = K([row[j] for row in h])
    torus, real = scalar_groups()
    if not c.is_zero():
        b = u**Q/c
        radius = a/c + b*b**Q
        root = radius.sqrt()
        return [f + (b + root*s)*g for s in torus]
    # Tr(u*t)=a gives the affine part of the isotropic projective line.
    z = F.gen()
    shift = a*z/(z+z**Q)
    return [g, *(f + ((s+shift)/u)*g for s in real)]


def product(polys):
    while len(polys) > 1:
        pairs = [a*b for a, b in zip(polys[::2], polys[1::2])]
        polys = pairs + (polys[-1:] if len(polys) % 2 else [])
    return polys[0]


def coefficient_norm(p):
    """Product of all twenty coefficient conjugates, returned as a binary polynomial."""
    coeffs = p.coeffs()
    value = K.one()
    for _ in range(20):
        value *= K(coeffs)
        coeffs = [c.frobenius(1) for c in coeffs]
    binary = value.coeffs()
    if any(not (c.is_zero() or c.is_one()) for c in binary):
        raise ArithmeticError("nonbinary coefficient norm")
    return polynomial(sum(int(c.is_one()) << i for i, c in enumerate(binary)))


def binary_factors(p):
    return {mask_of(g): int(e) for g, e in p.factor()[1]}


def relation(mask, row):
    h = matrix([element(v) for v in row["hermitian"]])
    t = K([element(v) for v in row["relative_factor"]])
    if t.degree() != 3 or not t.is_irreducible() or not t.leading_coefficient().is_one():
        raise ArithmeticError("invalid designated cubic")
    if set(binary_factors(coefficient_norm(t))) != {mask}:
        raise ArithmeticError("the cubic has the wrong binary norm")
    d = numerator(h)
    rest, remainder = divmod(d, t)
    if not remainder.is_zero() or any(p.degree() > 2 for p, _ in rest.factor()[1]):
        raise ArithmeticError("the cubic did not descend to relative degree two")
    pieces = pencil(h)
    source = sum((h[i][j] * T**(i+Q*j) for i in range(3) for j in range(3)), K.zero())
    if product(pieces).monic() != source.monic():
        raise ArithmeticError("the pencil did not reconstruct the full source polynomial")
    left = Counter()
    for piece in pieces:
        left.update(binary_factors(coefficient_norm(piece)))
    right = binary_factors(coefficient_norm(d))
    mult = right.pop(mask)
    inverse_q = pow(Q, -1, COFACTOR)
    coeff = Counter({p: e*inverse_q for p, e in left.items()})
    coeff.subtract(right)
    # The norm of h1(y)^2 is h1(y)^40 and h1 = T(T+1)^2.
    coeff.update({2: 40, 3: 80})
    inverse = pow(mult, -1, COFACTOR)
    return {p: (c*inverse) % COFACTOR for p, c in coeff.items() if c % COFACTOR}
