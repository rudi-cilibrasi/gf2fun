"""Check the finite column ranks and base polynomials for sparse prime-power degree drops."""

from collections import Counter
from itertools import combinations
from math import comb, prod

from check_cubed_parity import BINARY, X, polynomial
from check_safe_prime_powers import bits


def insert(pivots, value):
    while value:
        place = value.bit_length()-1
        if not pivots[place]:
            pivots[place] = value
            return True
        value ^= pivots[place]
    return False


def columns(ell, s):
    f = polynomial(range(ell)).factor()[1][0][0]
    t = f.degree()
    if t % s or not f.is_irreducible() or X.pow_mod(ell, f) != 1 or X % f == 1:
        raise ArithmeticError(f"incorrect primitive {ell}-th root model")
    # Project a field element into the subfield and test whether its first s
    # powers form a binary basis. This only needs a field generator, of any order.
    for mask in range(1, 1 << t):
        a = polynomial(i for i in range(mask.bit_length()) if mask >> i & 1)
        u = a.pow_mod(((1 << t)-1)//((1 << s)-1), f)
        basis = [u.pow_mod(i, f) for i in range(s)]
        pivots = [0]*t
        if u.pow_mod(1 << s, f) == u and all(insert(pivots, bits(v)) for v in basis):
            break
    else:
        raise ArithmeticError("no subfield basis")
    return t, [tuple(bits(b*X**i % f) for b in basis) for i in range(ell)]


def check_independence(ell, s, arity):
    t, blocks = columns(ell, s)

    def extend(start, left, basis):
        if not left:
            return 1
        count = 0
        for j in range(start, ell-left+1):
            enlarged = basis.copy()
            if not all(insert(enlarged, v) for v in blocks[j]):
                raise ArithmeticError(f"dependent columns at ell={ell}, s={s}, last column {j}")
            count += extend(j+1, left-1, enlarged)
        return count

    # Translation of exponents multiplies every column by a common nonzero scalar.
    initial = [0]*t
    if not all(insert(initial, v) for v in blocks[0]):
        raise ArithmeticError("dependent coefficient basis")
    count = extend(1, arity-1, initial)
    if count != comb(ell-1, arity-1):
        raise ArithmeticError("incomplete support enumeration")
    print(f"ell={ell}, base degree {s}: all {count} translated {arity}-column sets independent.")


def base_factors(ell, s, expected_minimum, expected_sparse=()):
    multiplier = (1 << s)-1
    target = X**(ell*multiplier)+1
    factors = target.factor()[1]
    if prod((f for f, _ in factors), start=BINARY.one()) != target:
        raise ArithmeticError("incomplete factorization")
    weights = Counter()
    sparse = set()
    for f, multiplicity in factors:
        if multiplicity != 1 or not f.is_irreducible():
            raise ArithmeticError("expected squarefree irreducible factors")
        if X.pow_mod(multiplier, f) == 1:
            continue
        support = tuple(i for i, c in enumerate(f.coeffs()) if c)
        weights[len(support)] += 1
        if len(support) <= 5:
            sparse.add(support)
    if min(weights) != expected_minimum or sparse != set(expected_sparse):
        raise ArithmeticError(f"unexpected sparse factors at {ell}: {weights}, {sparse}")
    print(f"ell={ell}: minimum weight {min(weights)} among {sum(weights.values())} eligible "
          f"factors of X^{ell*multiplier}+1; sparse bases {sorted(sparse)}.")


if __name__ == '__main__':
    for row in ((13, 2, 4), (17, 1, 4), (19, 2, 5), (19, 3, 5), (29, 4, 5),
                (29, 7, 4), (37, 4, 5), (37, 6, 5), (37, 9, 4), (43, 2, 4)):
        check_independence(*row)
    base43 = (0, 5, 7, 9, 14)
    base_factors(13, 2, 9)
    base_factors(17, 1, 5, [(0, 3, 4, 5, 8)])
    base_factors(29, 7, 9)
    base_factors(37, 9, 11)
    base_factors(43, 2, 5, [base43])
    for j in range(6):
        g = 3**j
        f = polynomial(g*e for e in base43)
        order = 129*g
        if not f.is_irreducible() or X.pow_mod(order, f) != 1 or any(
                X.pow_mod(order//p, f) == 1 for p in (3, 43)):
            raise ArithmeticError(f"incorrect 43rd-power exception in degree {14*g}")
    misses = Counter()
    for taps in combinations(range(1, 14), 3):
        f = polynomial((0, *taps, 14))
        if f.is_irreducible():
            misses[tuple(p for p in (3, 43, 127) if X.pow_mod(16383//p, f) == 1)] += 1
    if misses != {(): 42, (3,): 26, (43,): 4, (127,): 1}:
        raise ArithmeticError(f"unexpected degree-14 census: {misses}")
    print("Of 73 irreducible pentanomials of degree 14, 43 pass the tests for 3 and 43. "
          "Exactly one of those misses 127, leaving 42 primitive.")
