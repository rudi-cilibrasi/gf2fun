"""Verify the field embedding and subfield multiple for the degree-4112 pentanomial."""

import argparse
import json
from collections import Counter
from math import gcd, prod
from pathlib import Path

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


def frontier(record, cofactor, fixed=(), cutoff=0):
    pending = Counter()
    for p, e in record["initial"]["factors"]:
        pending[tuple(p)] += e
    for relation in record["relations"]:
        p = tuple(relation["target"])
        if p in fixed or len(p)-1 <= cutoff:
            continue
        weight = pending.pop(p, 0)
        if not weight:
            if not fixed and not cutoff:
                raise ValueError("relation does not eliminate a pending factor")
            continue
        for side, multiplier in (("right", relation["a"]), ("left", -1)):
            for factor, e in relation[side][1]:
                pending[tuple(factor)] += weight*multiplier*e
    return {p: weight % cofactor for p, weight in pending.items() if weight % cofactor}


def descend(record, field, ring, modulus, cofactor):
    for relation in record["relations"]:
        target = tuple(relation["target"])
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
    if ORDER//cofactor % ((K-1)*M):
        raise ValueError("the projection must kill the coordinate and all constants")
    return frontier(record, cofactor)


def contribution_values(files, record, cofactor):
    # Accept an ancestor as well as a leaf. A verified ancestor covers its entire subtree.
    allowed = {tuple(p) for p, _ in record["initial"]["factors"]}
    for relation in record["relations"]:
        for side in ("left", "right"):
            allowed.update(tuple(p) for p, _ in relation[side][1])
    values = {}
    for path in files:
        sheet = json.loads(path.read_text())
        if "cofactor" in sheet and sheet["cofactor"] != cofactor:
            raise ValueError(f"incorrect cofactor in {path}")
        for row in sheet["factors"]:
            e = row["exponent"]
            if e is None:
                continue
            p = tuple(row["coefficients"])
            if p not in allowed or any(type(c) is not int for c in p):
                raise ValueError(f"unrecognized factor in {path}")
            if type(e) is not int or not 0 <= e < cofactor:
                raise ValueError(f"invalid projected exponent in {path}")
            if p in values and values[p] != e:
                raise ValueError(f"conflicting exponents for {p}")
            values[p] = e
    if values:
        f, x, y, embed = field_coordinate(record)
        known = ORDER//cofactor
        base = x.pow_mod(known, f)
        for p, e in values.items():
            value = 0*x
            for c in reversed(p):
                value = (value*y + embed(c)) % f
            if value.pow_mod(known, f) != base.pow_mod(e, f):
                raise ValueError(f"incorrect logarithm for {p}")
    return values


def task_sheet(record, cofactor, files, cutoff, output):
    from check_4112_binomials import expand, orbits, read_rows

    supplied = contribution_values(files, record, cofactor)
    leaves = frontier(record, cofactor, supplied, cutoff)
    linear = expand(read_rows()[1], orbits(ConstantField(), record["unit"]))
    known_exponent = 0
    remaining = []
    for p, weight in sorted(leaves.items(), key=lambda item: (len(item[0]), item[0])):
        if p in supplied:
            e = supplied[p]
        elif len(p) == 2:
            e = linear[p[0]]
        else:
            signed = weight if 2*weight <= cofactor else weight-cofactor
            remaining.append({"coefficients": p, "multiplier": signed, "exponent": None})
            continue
        known_exponent = (known_exponent + weight*e) % cofactor
    if not remaining:
        f, x, y, _ = field_coordinate(record)
        t = polynomial(int(record["target_in_torsion_basis"], 16)).compose_mod(y, f)
        known = ORDER//cofactor
        if t.pow_mod(known, f) != x.pow_mod(known*known_exponent, f):
            raise ValueError("the assembled exponent does not match the pentanomial")
        print(f"Verified the assembled cofactor exponent. The target order has index "
              f"{gcd(known_exponent, cofactor)} given its archived known-prime tests.")
    if output:
        sheet = {"cofactor": cofactor, "known_exponent": known_exponent, "factors": remaining}
        output.write_text(json.dumps(sheet, indent=2) + "\n")
    print(f"Accepted {len(supplied)} contributed logarithms. "
          f"{len(remaining)} nonlinear factors remain at this cutoff.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tasks", type=Path, help="write the unresolved factors and their signed weights to JSON")
    parser.add_argument("--logs", type=Path, action="append", default=[],
                        help="verify and incorporate filled exponents from a task sheet (repeatable)")
    parser.add_argument("--max-degree", type=int, default=0,
                        help="stop descent early when a factor reaches this degree")
    args = parser.parse_args()
    if args.max_degree < 0:
        parser.error("--max-degree must be nonnegative")

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
    if args.tasks or args.logs or args.max_degree:
        task_sheet(record, ORDER//known, args.logs, args.max_degree, args.tasks)


if __name__ == "__main__":
    main()
