"""Check two free branches in the degree-1229 isogeny and linear Hermitian logarithm equations."""

import json
from math import gcd

from check_1229_elliptic_descent import OCTIC_BIVARIATES, octic_relation
from check_1229_hermitian_descent import F, H0, H1, Q, T, bits, relative_factor
from check_1229_isogeny_logs import pullback
from check_1229_power_images import SPLITS, split_log_table
from check_1229_terminal_census import RECORD, TABLES, catalogue, lookup
from check_degree_1229 import COFACTOR
from check_factor_base import DATA, irreducible, polynomial


PARENT = 0x1e7
BRANCHES = (
    (0x15f, 0x1100c6d95f5, 0x1077e6b3b13, 0x10015908c71c5643c20a5dd0d5160bd6135c0a13c6ddce8adc1),
    (0x1f5, 0x14c7172991f, 0x11109bd55fd5500619ab8f8fb519f94059251980335f670d865),
)


def pencil_rank(mask):
    """Binary rank on the 40 parameters of a linear Hermitian numerator, modulo one relative factor."""
    factor = relative_factor(mask)
    z = F.gen()
    real = z**(Q+1)
    columns = ([T*H0*real**i for i in range(10)] +
               [H1*real**i for i in range(10)] +
               [H0*(z**i)**Q + T*H1*z**i for i in range(20)])
    pivots = {}
    for column in columns:
        residue = column % factor
        value = sum(bits(c) << (20*i) for i, c in enumerate(residue.coeffs()))
        while value:
            lead = value.bit_length()-1
            if lead not in pivots:
                pivots[lead] = value
                break
            value ^= pivots[lead]
    return len(pivots)


def main():
    points = {p for branch in BRANCHES for p in branch}
    if (len(points) != sum(map(len, BRANCHES)) or PARENT in points or
            not irreducible(polynomial(PARENT)) or gcd(5*Q, COFACTOR) != 1):
        raise ArithmeticError("invalid branch labels or tail denominator")
    for branch in BRANCHES:
        degrees = [p.bit_length()-1 for p in branch]
        if degrees[0] != 8 or degrees[-1] != 200 or min(degrees[1:]) <= 8:
            raise ArithmeticError("a branch can reenter the octic layer or has the wrong terminal degree")
        for parent, child in zip((PARENT, *branch[:-1]), branch, strict=True):
            fiber = polynomial(pullback(parent))
            value = polynomial(child)
            if not irreducible(value) or fiber % value != 0 or fiber.derivative() % value == 0:
                raise ArithmeticError(f"{child:#x} is not a simple irreducible child of {parent:#x}")
            degree = value.degree()
            if degree//gcd(degree, 20) <= 6 and pencil_rank(child) != 40:
                raise ArithmeticError(f"a linear Hermitian numerator meets {child:#x}")
        print(f"Verified branch from {branch[0]:#x} with degrees {degrees}.")

    field_mask, table = split_log_table()
    if points.intersection(table) or any((p.bit_length()-1) % 200 == 0 for p in table):
        raise ArithmeticError("a split-table logarithm may belong to a perturbation branch")
    catalogues = []
    for _, path, count, digest in TABLES:
        data = catalogue(path, count, digest)
        catalogues.append(data)
        if any(p in points or (p.bit_length()-1) % 200 == 0 for p, _, _ in RECORD.iter_unpack(data)):
            raise ArithmeticError(f"a reference mask in {path.name} may belong to a perturbation branch")
    split = json.loads((DATA / SPLITS["elliptic-seven"]).read_text())["logarithms"]
    coefficients = {int(r["mask_hex"], 16): int(r["coefficient_mod_C"]) for r in split["remaining"]}
    target = BRANCHES[0][0]
    if (len(coefficients) != 7 or gcd(coefficients.pop(target), COFACTOR) != 1 or
            points.intersection(coefficients) or any((p.bit_length()-1) % 200 == 0 for p in coefficients)):
        raise ArithmeticError("the perturbation also changes another input, or has nonunit coefficient")

    expected = {"binary-32": [84, 473], "binary-128": [117, 377]}
    for method in OCTIC_BIVARIATES:
        rhs = octic_relation(method, polynomial(field_mask))
        missing = sorted(p.bit_length()-1 for p in rhs if p not in table and
                         all(lookup(data, p) is None for data in catalogues))
        if missing != expected[method] or any(d % 8 == 0 for d in missing):
            raise ArithmeticError(f"unexpected remaining logarithms for {method}")
        print(f"{method} gives two further inputs of binary degrees {missing}.")
    print("Both perturbation branches avoid the reference tables, every linear Hermitian numerator, "
          "and the other six inputs of the elliptic split.")


if __name__ == "__main__":
    main()
