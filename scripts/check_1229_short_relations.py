"""Verify every reported short-relation factor in the coordinate of the equation it solves."""

import csv
from math import gcd
from pathlib import Path

from check_degree_1229 import N
from check_sparse_root_models import X
from period_coordinate import mask_of


TABLE = Path(__file__).resolve().parents[1] / "data" / "degree-1229-short-relations.csv"
COLUMNS = ["degree", "tap", "weight_z", "weight_z_a", "weight_z_m", "weight_z_m_minus_a"]


def factor_mask(relation):
    # The degree-1229 part is unique below degree 2458. Neither binary scalar is a root.
    if relation(0) == 0 or relation(1) == 0:
        raise ArithmeticError("unexpected linear factor in a relation")
    factor = relation.gcd(X.pow_mod(1 << N, relation) + X)
    if factor.degree() != N:
        raise ArithmeticError("the relation has no degree-1229 factor")
    return mask_of(factor)


def add_reciprocal(masks, mask):
    masks.update((mask, int(f"{mask:b}"[::-1], 2)))


def main():
    parents, direct, translated = set(), set(), set()
    with TABLE.open(newline="") as source:
        reader = csv.reader(source)
        if next(reader) != COLUMNS:
            raise ValueError("incorrect table header")
        for row in reader:
            m, a, *weights = map(int, row)
            if not N <= m < 2*N or not 0 < a <= m//2 or gcd(a, m) != 1 or (m, a) in parents:
                raise ValueError(f"invalid normalized parent {(m, a)}")
            parents.add((m, a))
            # For z^m=1+z^a, use z, z^a, z^m, z^(m-a) as independent coordinates.
            relations = (X**m + X**a + 1, X**m + (X+1)**a,
                         X**a + (X+1)**m, X**a * (X+1)**(m-a) + 1)
            masks = [factor_mask(f) for f in relations]
            if [mask.bit_count() for mask in masks] != weights:
                raise ArithmeticError(f"incorrect minimal-polynomial weight at {(m, a)}")
            add_reciprocal(direct, masks[0])
            for mask in masks[1:]:
                add_reciprocal(translated, mask)
    if len(parents) != 539:
        raise ArithmeticError("incomplete factor list")
    print(f"Direct trinomial relations: {len(direct)} minimal polynomials, minimum weight "
          f"{min(p.bit_count() for p in direct)}.")
    print(f"Relations between a value and its translate: {len(translated)} minimal polynomials, "
          f"minimum weight {min(p.bit_count() for p in translated)}.")


if __name__ == "__main__":
    main()
