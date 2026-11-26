"""Verify the support overlaps for third, fifth and seventh powers of primitive trinomial roots."""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, gcd, lcm

from check_cubed_parity import X, polynomial
from check_cubing_chains import primitive


def power_support(support, m):
    """Support from the equal-residue or midpoint formula for a primitive trinomial."""
    for a, c in combinations(support, 2):
        if (c-a) % m == 0:
            b, = set(support) - {a, c}
            step = (c-a)//m
            block = {a+j*step for j in range(m+1) if comb(m, j) % 2}
            return tuple(sorted(block ^ {b}))
    for a, b, c in permutations(support):
        if (a+c-2*b) % m == 0 and m in (5, 7):
            t = (a+c-2*b)//m
            counts = Counter((*support, b+t, b+(m//2)*t))
            return tuple(sorted(e for e, count in counts.items() if count % 2))
    raise ValueError("a primitive trinomial of degree above seven must match one of the formulas")


def exceptional_degrees(points, original, equations):
    """Solve every affine ordering of the support condition over the rationals."""
    degrees = set()
    for chosen in permutations(points, len(equations[0])):
        parameters = set()
        for row in equations:
            a, b = (sum(c*p[i] for c, p in zip(row, chosen)) for i in range(2))
            if a:
                parameters.add(Fraction(-b, a))
            elif b:
                break
        else:
            if not parameters:
                raise ArithmeticError("the condition holds identically for this ordering")
            if len(parameters) != 1:
                continue
            s, = parameters
            if len({a*s+b for a, b in points}) != 5:
                continue
            roots = sorted(a*s+b for a, b in original)
            differences = [v-roots[0] for v in roots[1:]]
            scale = lcm(*(v.denominator for v in differences))
            tap, degree = (int(scale*v) for v in differences)
            degrees.add(degree//gcd(tap, degree))
    return degrees


def check_patterns():
    zero, one, two, three, four, five = ((0, i) for i in range(6))
    s = (1, 0)
    ap4 = [(1,-2,1,0), (0,1,-2,1)]
    configurations = [
        ([zero, one, four, five, s], [zero, five, s], ap4, set()),
        ([zero, one, two, s, (-1,5)], [zero, s, (-1,5)], ap4, {7}),
        ([zero, one, two, s, (-1,5)], [zero, s, (-1,5)], [(1,-1,-1,1)], {7}),
        ([zero, one, three, s, (-1,7)], [zero, s, (-1,7)], [(1,-2,1)], {2,5,9,11,13}),
        ([zero, one, three, s, (-1,7)], [zero, s, (-1,7)], [(1,-1,-1,1)], {5,9,11}),
    ]
    for points, source, equations, expected in configurations:
        if exceptional_degrees(points, source, equations) != expected:
            raise ArithmeticError("unexpected exceptional degrees for normalized supports")


def check_degree(n):
    sources = [(0, a, n) for a in range(1, n) if primitive(polynomial((0, a, n)), n)]
    family = {3: set(), 5: set(), 7: set()}
    for support in sources:
        f = polynomial(support)
        for m, outputs in family.items():
            powers = power_support(support, m)
            g = polynomial(powers)
            if g.degree() != n or g.compose_mod(X**m, f) != 0 or not g.is_irreducible():
                raise ArithmeticError("a power formula fails direct substitution or irreducibility")
            if n > 7:
                expected_weight = 9 if m == 7 and len({e % 7 for e in support}) == 2 else 5
                if len(powers) != expected_weight:
                    raise ArithmeticError("incorrect image weight")
            if gcd(m, 2**n-1) == 1 and len(powers) == 5:
                if powers in outputs or not primitive(g, n):
                    raise ArithmeticError("repeated or imprimitive image within one family")
                outputs.add(powers)
    overlaps = [(a, b, f) for a, b in combinations(family, 2) for f in family[a] & family[b]]
    if n == 7:
        if sorted(overlaps) != [(3, 5, (0,1,2,3,7)), (3, 5, (0,4,5,6,7))]:
            raise ArithmeticError("incorrect boundary examples")
    elif overlaps:
        raise ArithmeticError("overlap between the three families")
    return len(sources), [len(outputs) for outputs in family.values()]


def block_image(support, m):
    for a, b in combinations(support, 2):
        step, remainder = divmod(b-a, m)
        if not remainder:
            isolated, = set(support)-{a, b}
            return tuple(sorted((a, a+step, b-step, b, isolated)))
    return None


def check_all_blocks(n):
    sources = [(0, a, n) for a in range(1, n) if primitive(polynomial((0, a, n)), n)]
    exponents = [3, 5, 7, *(2**k+1 for k in range(3, n.bit_length()) if 2**k+1 <= n)]
    counts = Counter()
    images = set()
    for s in sources:
        for m in exponents:
            if gcd(2**n-1, m) != 1:
                continue
            t = power_support(s, m) if m <= 7 else block_image(s, m)
            if t is None or len(t) != 5:
                continue
            g = polynomial(t)
            if (len(set(t)) != 5 or t in images or not primitive(g, n)
                    or g.compose_mod(X**m, polynomial(s)) != 0):
                raise ArithmeticError(f"repeated or invalid power-{m} image at {s}")
            images.add(t)
            counts[m] += 1
    return len(sources), dict(sorted(counts.items()))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blocks", type=int, metavar="DEGREE", help="verify all binary block powers in one odd degree above 11")
    args = parser.parse_args()
    check_patterns()
    if args.blocks is not None:
        if args.blocks <= 11 or args.blocks % 2 == 0:
            parser.error("--blocks requires an odd degree above 11")
        total, counts = check_all_blocks(args.blocks)
        print(f"{total} primitive trinomials give {sum(counts.values())} different primitive pentanomials: {counts}.")
        raise SystemExit(0)
    if check_all_blocks(153) != (4, {3: 4, 5: 4, 9: 4, 17: 4}):
        raise ArithmeticError("incorrect degree-153 block families")
    for n in range(7, 18):
        total, counts = check_degree(n)
        print(f"Degree {n} has {total} primitive trinomials and "
              f"{counts[0]}, {counts[1]}, {counts[2]} primitive five-term images for powers 3, 5, 7.")
