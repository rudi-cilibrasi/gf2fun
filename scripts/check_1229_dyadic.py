"""Verify degree-halving identities in the binary degree-1229 field."""

import gzip
import json
from collections import Counter
from functools import cache

from check_1229_isogeny_logs import H1, Q
from check_degree_1229 import COFACTOR
from check_factor_base import DATA, polynomial


FIRST = DATA / "degree-1229-dyadic-level1.json.gz"


@cache
def first_level():
    with gzip.open(FIRST, "rt") as stream:
        return {int(mask, 16): row for mask, row in json.load(stream).items()}


def halving_relation(mask, edges, field):
    """Verify the unprojected norm identity before extracting its logarithmic coefficients."""
    degree = mask.bit_length() - 1
    m = degree // 2
    if degree % 40:
        raise ValueError("the binary target degree must be divisible by 40")
    source = residual = polynomial(1)
    relation = Counter({2: m, 3: 2*m})  # h1 = T(T+1)^2
    inverse = pow(Q, -1, COFACTOR)
    seen = set()
    for child, left, right in edges:
        d = child.bit_length() - 1
        if child in seen or d <= 0 or m % d or min(left, right) < 0 or not (left or right):
            raise ValueError("invalid child in a degree-halving certificate")
        seen.add(child)
        p = polynomial(child)
        if left:
            source = source * (p if left == 1 else p.pow_mod(left, field)) % field
        if right:
            residual = residual * (p if right == 1 else p.pow_mod(right, field)) % field
        relation[child] += inverse * left - right
    actual = (polynomial(mask) * residual % field).pow_mod(Q, field)
    expected = H1.pow_mod(m*Q, field) * source % field
    if actual != expected:
        raise ArithmeticError(f"the unprojected degree-halving identity failed at {mask:#x}")
    return relation


def halve_parents(relation, field):
    result = Counter()
    rows = first_level()
    for mask, weight in relation.items():
        edges = ((int(p, 16), a, b) for p, a, b in rows[mask]["children"])
        children = halving_relation(mask, edges, field)
        result.update({p: weight * e for p, e in children.items()})
    return result
