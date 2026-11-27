"""Verify the field embedding and subfield multiple for the degree-4112 pentanomial."""

import json
from collections import Counter
from math import prod

from flint import fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx

from check_factor_base import polynomial
from check_projective_4112 import BASE_TAPS, K, N, ORDER, Q, TABLE, ConstantField, field_and_root


DATA = TABLE.parent
DESCENT = DATA / "degree-4112-subfield-descent.json"
TARGET = DATA / "degree-4112-pentanomial-target.json"
M = Q + 1


def extension_rings():
    binary = fmpz_mod_poly_ctx(2)
    modulus = binary([int(i in BASE_TAPS) for i in range(17)])
    field = fq_default_ctx(modulus=modulus, var="a", fq_type="FQ_ZECH")
    return field, fq_default_poly_ctx(field)


def word(c):
    return sum(int(v) << i for i, v in enumerate(c.to_list()))


def element(field, c):
    if type(c) is not int or not 0 <= c < K:
        raise ValueError("invalid constant field encoding")
    return field([(c >> j) & 1 for j in range(16)])


def field_coordinate(record):
    f, x, a = field_and_root()
    alpha, beta = record["directions"]
    scale, unit = record["scale"], record["unit"]
    basis = [a**j for j in range(16)]

    def embed(c):
        if type(c) is not int or not 0 <= c < K:
            raise ValueError("invalid binary model coefficient")
        return sum((basis[j] for j in range(16) if c >> j & 1), 0*x)

    gcd, inverse, _ = (x + embed(beta)).xgcd(f)
    if gcd != 1:
        raise ValueError("pole in the change of coordinates")
    y = embed(scale) * (x + embed(alpha)) * inverse % f
    if y.pow_mod(M, f) != embed(unit) or y.pow_mod(M, f) == 1 or y.pow_mod(M*M, f) != 1:
        raise ValueError("invalid torsion coordinate")
    if pow(2, N//2, M*M) != M*M-1 or pow(2, N//257, M*M) == 1:
        raise ValueError("incorrect degree or involution for the torsion coordinate")
    return f, x, y, embed


def power_basis(record, field):
    bits = int(record["target_in_torsion_basis"], 16)
    if not 0 < bits < 2**N:
        raise ValueError("invalid binary power-basis representation")
    unit = element(field, record["unit"])
    basis = [unit**j for j in range(16)]
    tower = [sum((basis[j] for j in range(16) if bits >> (M*j+i) & 1), field.zero())
             for i in range(M)]
    return polynomial(bits), tower


def check_embedding(record, field):
    f, x, y, _ = field_coordinate(record)
    target = sum(x**i for i in (0, 1, 12, 23, N))
    coordinate, tower = power_basis(record, field)
    t = coordinate.compose_mod(y, f)
    if target.compose_mod(t, f) != 0:
        raise ValueError("the supplied element is not a root of the pentanomial")
    g = x.pow_mod(record["matching_power"] * (ORDER//(M*M)), target)
    if coordinate.compose_mod(g, target) != x:
        raise ValueError("inverse coordinate failed in the sparse field")
    return tower


def frobenius_rank(t, modulus, ring):
    # Use logarithm tables only in the 16-bit constant field. Each column
    # contains the coefficients of t^i (t^Q)^j in the relative power basis.
    small = ConstantField()
    exp = small.exp * 2
    log = small.log
    t_q = t.pow_mod(Q, modulus)
    powers = [ring.one()]
    conjugates = [ring.one()]
    for _ in range(15):
        powers.append(powers[-1]*t % modulus)
        conjugates.append(conjugates[-1]*t_q % modulus)
    pivots = {}
    for left in powers:
        for right in conjugates:
            entries = [word(c) for c in (left*right % modulus).coeffs()]
            entries.extend([0] * (M-len(entries)))
            for i in range(M):
                if not entries[i]:
                    continue
                multiplier = log[entries[i]]
                if i not in pivots:
                    pivots[i] = [(j, (log[v]-multiplier) % (K-1))
                                 for j, v in enumerate(entries) if v]
                    break
                for j, exponent in pivots[i]:
                    entries[j] ^= exp[multiplier+exponent]
    return len(pivots)


def involution(value, inverse_unit, ring):
    # The halfway binary Frobenius sends y to 1/y and c in k to c^256.
    coefficients = value.coeffs()
    coefficients.extend([inverse_unit*0] * (M-len(coefficients)))
    return ring([coefficients[0].frobenius(8)]
                + [inverse_unit*c.frobenius(8) for c in coefficients[:0:-1]])


def factor_product(factors, lead, field, ring):
    result = ring([element(field, lead)])
    degrees = []
    for row, multiplicity in factors:
        if type(multiplicity) is not int or multiplicity < 1:
            raise ValueError("invalid factor multiplicity")
        p = ring([element(field, c) for c in row])
        if p.degree() < 1 or not p.is_monic() or not p.is_irreducible():
            raise ValueError("invalid monic irreducible factor")
        result *= p**multiplicity
        degrees.extend([p.degree()]*multiplicity)
    return result, sorted(degrees)


def descend(record, field, ring, modulus, cofactor):
    # The signed coefficients are exponents in the projected multiplicative group.
    pending = Counter()
    for p, e in record["initial"]["factors"]:
        pending[tuple(p)] += e
    for relation in record["relations"]:
        target = tuple(relation["target"])
        weight = pending.pop(target, 0)
        if not weight:
            raise ValueError("relation does not eliminate a pending factor")
        a, b = relation["a"], relation["b"]
        if not 1 <= a < Q or a & (a-1) or not 0 <= b < M:
            raise ValueError("invalid Frobenius or torsion exponent")
        left_lead, left = relation["left"]
        right_lead, right = relation["right"]
        lower, _ = factor_product(left, left_lead, field, ring)
        upper, _ = factor_product(right, right_lead, field, ring)
        h = ring([element(field, c) for c in target])
        if (h*lower - ring.gen()**b * upper.pow_mod(a, modulus)) % modulus:
            raise ValueError("invalid multiplicative descent identity")
        for factors, multiplier in ((right, a), (left, -1)):
            for p, e in factors:
                pending[tuple(p)] += weight*multiplier*e
    if ORDER//cofactor % ((K-1)*M):
        raise ValueError("the projection must kill the coordinate and all constants")
    return {p: weight % cofactor for p, weight in pending.items() if weight % cofactor}


def main():
    record = json.loads(DESCENT.read_text())
    known = prod(json.loads(TARGET.read_text())["known_prime_factors"])
    if ORDER % known or known % (2**(N//2)-1):
        raise ValueError("the known order part does not kill the subfield")
    field, ring = extension_rings()
    unit = element(field, record["unit"])
    modulus = ring.gen()**M + unit
    t = ring(check_embedding(record, field))
    rank = frobenius_rank(t, modulus, ring)
    if rank != 256:
        raise ValueError(f"unexpected Frobenius rank {rank}")
    initial = record["initial"]
    numerator, degrees = factor_product(initial["factors"], initial["lead"], field, ring)
    inv = 1/unit
    if numerator.degree() != sum(degrees) or numerator.degree() >= M:
        raise ValueError("invalid initial representative")
    if (involution(t, inv, ring)*numerator - t*involution(numerator, inv, ring)) % modulus:
        raise ValueError("the candidate and the factored representative differ outside the subfield")
    print(f"Verified mutually compatible coordinates, relative Frobenius rank {rank}, "
          f"and a subfield multiple with factor degrees {degrees}.")
    leaves = descend(record, field, ring, modulus, ORDER//known)
    census = Counter(len(p)-1 for p in leaves if len(p)>2)
    print(f"Verified {len(record['relations'])} descent identities. "
          f"The remaining nonlinear factors by degree are {dict(sorted(census.items()))}.")


if __name__ == "__main__":
    main()
