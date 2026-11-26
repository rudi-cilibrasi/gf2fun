"""Verify short Frobenius relations and transport both sparse roots to their fields."""

import argparse
import json

from check_1229_subgroup_traces import multiplication_table, multiply
from check_factor_base import DATA, modulus, polynomial
from period_coordinate import CANDIDATES, DEGREE, coordinate, mask_of


MODELS = ((256, 103, 4), (1024, 37, 10))
TABLE = DATA / "degree-1229-frobenius-models.json"


def power_basis_expression(generator, value, field):
    """Express a polynomial residue in the power basis of a second generator."""
    n = field.bit_length() - 1
    table = multiplication_table(generator, field)
    basis = {}
    column = 1
    for i in range(n):
        v, expression = column, 1 << i
        while v:
            lead = v.bit_length() - 1
            if lead not in basis:
                basis[lead] = (v, expression)
                break
            entry, coefficients = basis[lead]
            v ^= entry
            expression ^= coefficients
        if not v:
            raise ArithmeticError("the proposed generator has deficient degree")
        column = multiply(column, table)
    expression = 0
    while value:
        entry, coefficients = basis[value.bit_length() - 1]
        value ^= entry
        expression ^= coefficients
    return polynomial(expression)


def primitive_generator_in(field):
    """Transport the certified q=1024 generator through the common Gauss-period coordinate."""
    model = next(row for row in json.loads(TABLE.read_text()) if row["q"] == 1024)
    certificate = json.loads((DATA / "degree-1229-q1024-certificate.json").read_text())
    if model["modulus_hex"] != certificate["modulus_hex"]:
        raise ValueError("the dense modulus differs from the primitive-generator certificate")
    old = int(model["modulus_hex"], 16)
    expression = power_basis_expression(int(model["period_hex"], 16), 2, old)
    generator = expression.compose_mod(coordinate(field), field)
    if polynomial(old).compose_mod(generator, field) != 0:
        raise ArithmeticError("the transported generator fails its certified minimal polynomial")
    return generator


def make_records():
    x = polynomial(2)
    sparse = {name: modulus(DEGREE, taps) for name, taps in CANDIDATES.items()}
    roots_in_period = {}
    for name, f in sparse.items():
        period = coordinate(f)
        root = power_basis_expression(mask_of(period), 2, mask_of(f))
        if root.compose_mod(period, f) != x:
            raise ArithmeticError("the change of basis failed")
        roots_in_period[name] = root
    records = []
    for q, numerator, denominator in MODELS:
        h0, h1 = polynomial(numerator), polynomial(denominator)
        y = x**q
        parent = h0(y) + x*h1(y)
        factors = parent.factor()[1]
        chosen = [f for f, e in factors if f.degree() == DEGREE and e == 1]
        if len(chosen) != 1:
            raise ArithmeticError("expected a unique simple factor of the target degree")
        f, = chosen
        if h1.compose_mod(y % f, f) == 0 or parent % f != 0:
            raise ArithmeticError("invalid Frobenius representation")
        period = coordinate(f)
        roots = {name: root.compose_mod(period, f) for name, root in roots_in_period.items()}
        for name, root in roots.items():
            if sparse[name].compose_mod(root, f) != 0:
                raise ArithmeticError(f"the embedded {name} root failed its sparse equation")
        records.append({
            "q": q, "numerator_mask": numerator, "denominator_mask": denominator,
            "parent_degrees": [[g.degree(), e] for g, e in sorted(factors, key=lambda t: t[0].degree())],
            "modulus_hex": hex(mask_of(f)), "period_hex": hex(mask_of(period)),
            "sparse_root_hex": {name: hex(mask_of(root)) for name, root in roots.items()},
        })
    return records


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit", action="store_true", help="write the model records to standard output")
    args = parser.parse_args()
    records = make_records()
    if args.emit:
        print(json.dumps(records, indent=2))
    else:
        if json.loads(TABLE.read_text()) != records:
            raise ArithmeticError("the published field records differ from reconstruction")
        for row in records:
            print(f"q = {row['q']}, degree {DEGREE} verified with both sparse roots in the same period coordinate.")
