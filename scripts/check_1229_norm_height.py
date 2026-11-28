"""Check direct norm quotients for both sparse roots and certify their minimum total degree."""

import argparse
import json
from collections import Counter
from functools import cache
from math import gcd

from check_degree_1229 import COFACTOR, check_known_order
from check_factor_base import DATA, irreducible, modulus, polynomial
from period_coordinate import CANDIDATES, DEGREE, mask_of


CERTIFICATE = DATA / "degree-1229-q1024-norm-quotients.json"
KNOWN_OFFSETS = DATA / "degree-1229-known-offset-quotients.json"
FORMS = {"pair31": (31, 31), "pair32": (32, 32), "single62": (62, 0), "single64": (64, 0)}


def sparse_root(name, field):
    sparse = modulus(DEGREE, CANDIDATES[name])
    if not irreducible(sparse):
        raise ValueError("the proposed sparse polynomial is reducible")
    check_known_order(sparse)
    task = json.loads((DATA / f"degree-1229-single-log-{name}.json").read_text())
    if int(task["model_modulus_hex"], 16) != mask_of(field):
        raise ValueError("the sparse root uses another model modulus")
    root = polynomial(int(task["sparse_root_in_model_hex"], 16))
    if root.degree() >= DEGREE or sparse.compose_mod(root, field) != 0:
        raise ArithmeticError("invalid root of the designated pentanomial")
    return root


@cache
def certificate():
    rows = json.loads(CERTIFICATE.read_text())
    if rows["constant_field_modulus_hex"] != "0x100009":
        raise ValueError("unexpected basis for the constant field")
    return rows


def checked_norm(piece, degree, power=1):
    from check_1229_hermitian_descent import K, coefficient_norm, element

    binary = polynomial(int(piece["mask_hex"], 16))
    coeffs = piece["relative_factor"]
    if len(coeffs) != degree + 1 or coeffs[-1] != 1 or binary.degree() * power != 20 * degree:
        raise ValueError("incorrect degrees or leading coefficient in norm certificate")
    factor = K([element(c) for c in coeffs])
    if not factor.is_irreducible() or not irreducible(binary) or coefficient_norm(factor) != binary**power:
        raise ArithmeticError("incorrect irreducible factor or coefficient norm")
    return binary


def norm_quotient(name, form, root, field):
    row = certificate()["candidates"][name]["forms"][form]
    j = row["frobenius"]
    if not 0 <= j < DEGREE:
        raise ValueError("invalid Frobenius exponent")
    numerator_degree, denominator_degree = FORMS[form]
    u = checked_norm(row["numerator"], numerator_degree)
    v = polynomial(1)
    if denominator_degree:
        v = checked_norm(row["denominator"], denominator_degree)
    elif "denominator" in row:
        raise ValueError("a single-factor task requires denominator one")
    if (root.pow_mod(1 << j, field) * v - u) % field != 0 or u.gcd(v) != 1:
        raise ArithmeticError("the norm quotient does not represent the specified conjugate")
    inverse = pow(pow(2, j, COFACTOR), -1, COFACTOR)
    relation = {mask_of(u): inverse}
    if denominator_degree:
        relation[mask_of(v)] = -inverse
    return relation


def known_offset_quotient(name, root, field, table, discovery=None):
    if discovery is None:
        row = json.loads(KNOWN_OFFSETS.read_text())[name]
    else:
        from check_1229_hermitian_descent import K, bits

        row = json.loads(discovery.read_text())
        mask = int(row["unknown_mask_hex"], 16)
        row["unknown"] = None
        if mask != 1:
            binary = polynomial(mask)
            if not irreducible(binary):
                raise ValueError("the proposed unknown factor is reducible")
            split = K([int(c) for c in binary.coeffs()]).factor()[1]
            coeffs = min([bits(c) for c in f.coeffs()] for f, _ in split)
            row["unknown"] = {"mask_hex": hex(mask), "relative_factor": coeffs}
    j, shift = row["frobenius"], row["multiplier_power"]
    multiplier, small, denominator = (polynomial(int(row[key], 16)) for key in
                                     ("multiplier_hex", "known_numerator_hex", "known_denominator_hex"))
    if not 0 <= j < DEGREE or shift < 0 or any(p.is_zero() for p in (multiplier, small, denominator)):
        raise ValueError("invalid known multiplier, numerator, denominator or exponent")
    unknown = polynomial(1)
    if row["unknown"] is not None:
        absolute_degree = int(row["unknown"]["mask_hex"], 16).bit_length() - 1
        conjugates = gcd(absolute_degree, 20)
        unknown = checked_norm(row["unknown"], absolute_degree // conjugates, 20 // conjugates)
    u = small * unknown
    value = root.pow_mod(1 << j, field) * multiplier.pow_mod(shift, field)
    if (value * denominator - u) % field != 0 or u.gcd(denominator) != 1:
        raise ArithmeticError("the known-offset quotient fails in the field")
    relation = Counter()
    for p, weight in ((small, 1), (denominator, -1), (multiplier, -shift)):
        for factor, e in p.factor()[1]:
            mask = mask_of(factor)
            if 20 % factor.degree() or mask not in table:
                raise ArithmeticError("missing original linear-base logarithm in the offset")
            relation[mask] += weight * int(e)
    if not unknown.is_one():
        relation[mask_of(unknown)] += 1
    inverse = pow(pow(2, j, COFACTOR), -1, COFACTOR)
    return {p: inverse * e for p, e in relation.items()}


def is_coefficient_norm(p):
    """An irreducible of degree d occurs in a norm with multiplicity divisible by 20/gcd(20,d)."""
    return all(e % (20 // gcd(20, factor.degree())) == 0 for factor, e in p.factor()[1])


def audit_height(root, field):
    """Every reduced fraction of total binary degree below deg(field) is a convergent."""
    limit = 20 * 61
    candidates = 0
    w = root
    for j in range(DEGREE):
        previous, numerator = field, w
        previous_denominator, denominator = polynomial(0), polynomial(1)
        while not numerator.is_zero():
            m, n = numerator.degree(), denominator.degree()
            if m + n <= limit and m % 20 == n % 20 == 0:
                candidates += 1
                if is_coefficient_norm(numerator) and is_coefficient_norm(denominator):
                    raise ArithmeticError(f"smaller norm quotient at conjugate {j}, degrees {m}, {n}")
            q, remainder = divmod(previous, numerator)
            previous, numerator = numerator, remainder
            previous_denominator, denominator = denominator, previous_denominator + q * denominator
        w = w.pow_mod(2, field)
        if (w == root) != (j + 1 == DEGREE):
            raise ArithmeticError("unexpected Frobenius orbit length")
    return candidates


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", choices=CANDIDATES)
    args = parser.parse_args()
    model = json.loads((DATA / "degree-1229-q1024-certificate.json").read_text())
    field = polynomial(int(model["modulus_hex"], 16))
    if field.degree() != DEGREE or not irreducible(field):
        raise ValueError("invalid model field")
    for name in ([args.candidate] if args.candidate else CANDIDATES):
        root = sparse_root(name, field)
        for form in FORMS:
            norm_quotient(name, form, root, field)
        count = audit_height(root, field)
        if count != certificate()["candidates"][name]["convergents_with_eligible_degrees"]:
            raise ArithmeticError("unexpected number of convergents to test for coefficient norms")
        print(f"{name}: checked {DEGREE} conjugates, rejected {count} eligible fractions. "
              "Minimum total norm degree 62, minimum maximum degree 31.")


if __name__ == "__main__":
    main()
