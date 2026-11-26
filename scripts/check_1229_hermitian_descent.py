"""Factor certified Hermitian equations and take their binary norms in the degree-1229 model."""

import json
from collections import Counter
from functools import cache
from itertools import combinations
from math import gcd

from flint import fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx

from check_1229_isogeny_logs import Q
from check_degree_1229 import COFACTOR
from check_factor_base import DATA, irreducible, polynomial
from period_coordinate import mask_of


CERTIFICATES = DATA / "degree-1229-hermitian-descents.json"
DYADIC_TERMINALS = DATA / "degree-1229-dyadic-quadratic-logs.json"
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


def relative_factor(mask):
    if mask < 2 or not irreducible(polynomial(mask)):
        raise ValueError("choose a nonconstant binary irreducible mask")
    binary = K([mask >> i & 1 for i in range(mask.bit_length())])
    return min((p for p, _ in binary.factor()[1]), key=lambda p: tuple(bits(v) for v in p.coeffs()))


def records():
    rows = json.loads(CERTIFICATES.read_text()) + json.loads(DYADIC_TERMINALS.read_text())
    result = {int(r["mask_hex"], 16): r for r in rows}
    if len(rows) != len(result):
        raise ValueError("repeated Hermitian target")
    return result


def matrix(values):
    if len(values) == 3:
        a, b, u = values
        h = [[a, u], [u**Q, b]]
    else:
        a, b, c, u, v, w = values
        h = [[a, u, v], [u**Q, b, w], [v**Q, w**Q, c]]
    if any(row[i] != row[i]**Q for i, row in enumerate(h)):
        raise ValueError("non-Hermitian diagonal")
    return h


def numerator(h):
    m = len(h)-1
    return sum((c * (H0**i * H1**(m-i) * T**j)
                for i, row in enumerate(h) for j, c in enumerate(row)), K.zero())


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
    for i, j in combinations(range(len(h)), 2):
        a, c, u = h[i][i], h[j][j], h[i][j]
        if not (a*c + u*u**Q).is_zero():
            break
    else:
        if len(h) == 2:
            for i in range(2):
                if not h[i][i].is_zero():
                    # Rank one gives the norm of one column, up to its diagonal entry.
                    return [K([row[i] for row in h])] * (Q+1)
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
    m = len(h)-1
    t = K([element(v) for v in row["relative_factor"]])
    if t.degree() != m+1 or not t.is_irreducible() or not t.leading_coefficient().is_one():
        raise ArithmeticError("invalid designated target factor")
    if set(binary_factors(coefficient_norm(t))) != {mask}:
        raise ArithmeticError("the target factor has the wrong binary norm")
    d = numerator(h)
    rest, remainder = divmod(d, t)
    partner = int(row["quadratic_partner_hex"], 16) if "quadratic_partner_hex" in row else None
    bound = 2 if partner is not None and m == 1 else m
    if not remainder.is_zero() or any(p.degree() > bound for p, _ in rest.factor()[1]):
        raise ArithmeticError("a factor exceeds the proposed descent bound")
    pieces = pencil(h)
    source = sum((c * T**(i+Q*j) for i, row in enumerate(h) for j, c in enumerate(row)), K.zero())
    if product(pieces).monic() != source.monic():
        raise ArithmeticError("the pencil did not reconstruct the full source polynomial")
    left = Counter()
    for piece in pieces:
        left.update(binary_factors(coefficient_norm(piece)))
    right = binary_factors(coefficient_norm(d))
    mult = right.pop(mask)
    if partner is not None:
        nonlinear = {p for p in right if 20 % (p.bit_length()-1) != 0}
        degree = partner.bit_length()-1
        if (m != 1 or nonlinear != {partner} or degree // gcd(degree, 20) != 2
                or right[partner] != mult):
            raise ArithmeticError("the circle does not give the claimed pair of quadratic factors")
    inverse_q = pow(Q, -1, COFACTOR)
    coeff = Counter({p: e*inverse_q for p, e in left.items()})
    coeff.subtract(right)
    # Norm(h1(y)^m) = h1(y)^(20m) and h1 = T(T+1)^2.
    coeff.update({2: 20*m, 3: 40*m})
    inverse = pow(mult, -1, COFACTOR)
    return {p: (c*inverse) % COFACTOR for p, c in coeff.items() if c % COFACTOR}
