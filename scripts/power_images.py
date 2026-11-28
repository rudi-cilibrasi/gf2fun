"""Root-of-unity norm patterns for binary polynomials under third, fifth and seventh powering."""

from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement
from math import gcd

from check_cubed_supports import restrict


@cache
def root_multipliers(m):
    """Multiplication by powers of a primitive m-th root in a small binary field."""
    field = {3: 0b111, 5: 0b11111, 7: 0b1011}[m]
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


def residue_profiles(m):
    """Five labels modulo translation, invertible scaling and permutation."""
    return sorted({min(tuple(sorted(a*(r-b) % m for r in residues))
                       for a in range(1, m) for b in residues)
                   for residues in combinations_with_replacement(range(m), 5)
                   if len(set(residues)) > 1})


def direction(vector):
    divisor = gcd(*vector)
    if next(x for x in vector if x) < 0:
        divisor = -divisor
    return tuple(x//divisor for x in vector)


def classify_profile(m, residues, in_family=None):
    """Enumerate normalized sparse norms outside any recognized parametric family."""
    pattern = norm_pattern(m, residues)
    exceptions = set()
    if len(pattern) % 2 == 0:
        return exceptions

    @cache
    def visit(points):
        if len(set(points)) < 5:
            return
        columns = tuple(zip(*points))
        terms = Counter(tuple(sum(i*x for i, x in zip(mix, col)) for col in columns)
                        for mix in pattern)
        odd = sorted(t for t, multiplicity in terms.items() if multiplicity % 2)
        if len(odd) <= 5:
            if in_family and in_family(points, residues):
                return
            raise ArithmeticError(f"positive-dimensional sparse family for {residues}: {points}")
        if len(columns) > 2:
            # At least one of any six survivors must collide with another survivor.
            equations = {direction(tuple(a-b for a, b in zip(t, u)))
                         for i, t in enumerate(odd[:6]) for u in odd[i+1:]}
            for equation in equations:
                visit(restrict(points, equation))
            return

        # On a line every collision has the same normal direction. A colliding
        # pair removes at most two terms, including when several pairs coincide.
        pairs = Counter(direction((a-c, b-d)) for (a, b), (c, d) in combinations(odd, 2))
        for (u, v), count in pairs.items():
            if 2*count < len(odd)-5:
                continue
            values = [v*a-u*b for a, b in points]
            if len(set(values)) != 5:
                continue
            scale = gcd(*values)
            exponents = [x//scale for x in values]
            if not any(all((k*x-r) % m == 0 for x, r in zip(exponents, residues)) for k in range(1, m)):
                continue
            image = Counter(v*a-u*b for a, b in odd)
            if sum(c % 2 for c in image.values()) <= 5:
                support = tuple(x-min(exponents) for x in sorted(exponents))
                if in_family and in_family([(e,) for e in support], [e % m for e in support]):
                    continue
                exceptions.update((support, tuple(support[-1]-e for e in reversed(support))))

    visit(((0, 0, 0, 0), *(tuple(int(i == j) for j in range(4)) for i in range(4))))
    visit.cache_clear()
    return exceptions


def power_characteristic(support, m):
    """Characteristic polynomial of multiplication by X^m modulo F, including reducible F."""
    from flint import nmod_mat

    n = support[-1]
    modulus = sum(1 << e for e in support)
    column = 1
    transpose = []
    for i in range(n+m):
        if i >= m:
            transpose.extend((column >> j) & 1 for j in range(n))
        column <<= 1
        if column >> n:
            column ^= modulus
    coefficients = nmod_mat(n, n, transpose, 2).charpoly()
    return tuple(i for i in range(n+1) if coefficients[i])
