"""Root-of-unity norm patterns for binary polynomials under fifth and seventh powering."""

from functools import cache


@cache
def root_multipliers(m):
    """Multiplication by powers of a primitive m-th root in a small binary field."""
    field = {5: 0b11111, 7: 0b1011}[m]
    size = 1 << (field.bit_length()-1)
    rows = [list(range(size))]
    for _ in range(m):
        rows.append([(a << 1) ^ (field if (a << 1) >= size else 0) for a in rows[-1]])
    if rows[m] != rows[0] or len({row[1] for row in rows[:m]}) != m:
        raise ArithmeticError("invalid primitive root of unity")
    return rows[:m]


@cache
def norm_pattern(m, residues):
    """Monomial multiplicities with nonzero coefficients in the root-of-unity product."""
    multiples = root_multipliers(m)
    coefficients = {(0,)*len(residues): 1}
    for j in range(m):
        result = {}
        for counts, coefficient in coefficients.items():
            for i, exponent in enumerate(residues):
                next_counts = counts[:i] + (counts[i]+1,) + counts[i+1:]
                term = multiples[j*exponent % m][coefficient]
                result[next_counts] = result.get(next_counts, 0) ^ term
        coefficients = {k: v for k, v in result.items() if v}
    if any(c != 1 or sum(k*e for k, e in zip(counts, residues)) % m
           for counts, c in coefficients.items()):
        raise ArithmeticError("the norm failed descent to the base field")
    return tuple(coefficients)
