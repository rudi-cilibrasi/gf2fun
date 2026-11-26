"""Check direct norm quotients for both sparse roots and certify their minimum total degree."""

import argparse
import json
from functools import cache
from math import gcd

from check_degree_1229 import COFACTOR, check_known_order
from check_factor_base import DATA, irreducible, modulus, polynomial
from period_coordinate import CANDIDATES, DEGREE, mask_of


CERTIFICATE = DATA / "degree-1229-q1024-norm-quotients.json"
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


def checked_norm(piece, degree):
    from check_1229_hermitian_descent import K, coefficient_norm, element

    binary = polynomial(int(piece["mask_hex"], 16))
    coeffs = piece["relative_factor"]
    if len(coeffs) != degree + 1 or coeffs[-1] != 1 or binary.degree() != 20 * degree:
        raise ValueError("incorrect degrees or leading coefficient in norm certificate")
    factor = K([element(c) for c in coeffs])
    if not factor.is_irreducible() or not irreducible(binary) or coefficient_norm(factor) != binary:
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
