"""Certify finiteness of the first three equations for product-one quartets."""

from itertools import combinations, permutations
from math import prod

from make_witnesses import mask_product, remainder


# F16 = F2[B]/(B^4+B+1). Each element is the mask of its four coefficients.
MUL = [[remainder(mask_product(a, b), 0x13) for b in range(16)] for a in range(16)]


def unit_power(a, n):
    result = 1
    for _ in range(n % 15):
        result = MUL[result][a]
    return result


class Laurent(dict):
    """A Laurent polynomial in t,p with nonzero F16 coefficients."""

    def __add__(self, other):
        result = Laurent(self)
        for index, coefficient in other.items():
            combined = result.get(index, 0) ^ coefficient
            if combined:
                result[index] = combined
            else:
                del result[index]
        return result

    def __mul__(self, other):
        result = {}
        for (t, p), a in self.items():
            for (u, q), b in other.items():
                index = t + u, p + q
                result[index] = result.get(index, 0) ^ MUL[a][b]
        return Laurent((index, c) for index, c in result.items() if c)


def monomial(t=0, p=0, coefficient=1):
    return Laurent({(t, p): coefficient})


ONE = monomial()
ZERO = Laurent()


def image_coefficients(u, v, w):
    """First three characteristic coefficients of multiplication by h modulo H."""
    def shift(column):
        a, b, c, d = column
        return d, a + w*d, b + v*d, c + u*d

    power = (ONE, ZERO, ZERO, ZERO)
    column = (ZERO, ZERO, ZERO, ZERO)
    for exponent in range(6):
        if exponent in (0, 2, 3, 5):
            column = tuple(a + b for a, b in zip(column, power))
        power = shift(power)
    columns = [column]
    for _ in range(3):
        columns.append(shift(columns[-1]))

    def minors(size):
        total = ZERO
        for sites in combinations(range(4), size):
            for perm in permutations(sites):
                total += prod((columns[i][j] for i, j in zip(sites, perm)), start=ONE)
        return total

    return tuple(minors(size) for size in (1, 2, 3))


def defect(u, v, w):
    t, a, b = u + v + w, u + v + ONE, v + w + ONE
    return t*t*t * (a*a + a*b + b*b) + ONE


def evaluate_t(f, value):
    result = ZERO
    for (t, p), a in f.items():
        result += monomial(p=p, coefficient=MUL[a][unit_power(value, t)])
    return result


def normalize_p(f):
    offset = min(p for _, p in f)
    return {p-offset: a for (_, p), a in f.items()}


def univariate_remainder(a, b):
    result = dict(a)
    degree = max(b)
    inverse = unit_power(b[degree], -1)
    while result and (shift := max(result) - degree) >= 0:
        scale = MUL[result[degree + shift]][inverse]
        for i, c in b.items():
            j = i + shift
            combined = result.get(j, 0) ^ MUL[scale][c]
            if combined:
                result[j] = combined
            else:
                del result[j]
    return result


def check_quartic_fiber():
    beta = 2
    omega = unit_power(beta, 5)
    t, p, q = monomial(t=1), monomial(p=1), monomial(t=-3, p=-1)
    b = p + q
    a = monomial(coefficient=MUL[omega][omega])*p + monomial(coefficient=omega)*q
    quartic = (t + b + ONE, t + a + b, t + a + ONE)
    if defect(*quartic) != ZERO:
        raise ArithmeticError("incorrect parameterization of the product-one equation")

    first_image = image_coefficients(*quartic)
    first = defect(*first_image)
    low, high = min(p for _, p in first), max(p for _, p in first)
    endpoints = Laurent((k, c) for k, c in first.items() if k[1] in (low, high))
    if endpoints != monomial(t=-57, p=-19) + monomial(p=19):
        raise ArithmeticError("the two extreme Laurent coefficients are incorrect")

    specialized = tuple(evaluate_t(f, beta) for f in first_image)
    first_at_beta = evaluate_t(first, beta)
    second_at_beta = defect(*image_coefficients(*specialized))
    left, right = normalize_p(first_at_beta), normalize_p(second_at_beta)
    degrees = max(left), max(right)
    while right:
        left, right = right, univariate_remainder(left, right)
    if max(left) != 0:
        raise ArithmeticError("the specialized defects share a nonzero root")
    print(f"First defect has {len(first)} terms; its extreme terms are t^-57 p^-19 and p^19.")
    print(f"At t=beta the normalized defect degrees are {degrees}; their monic gcd is 1.")


if __name__ == "__main__":
    check_quartic_fiber()
