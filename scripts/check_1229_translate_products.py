"""Classify two ways of factoring the five original monomials into low-degree values."""

from collections import Counter, defaultdict
from itertools import combinations
from math import gcd, lcm

from sympy import Matrix

from check_degree_1229 import GROUP, N, check_known_order
from check_factor_base import modulus
from check_sparse_root_models import X, irreducible_candidate, small_factors


def quadratic_smooth_supports():
    # A constant-one polynomial with irreducible factors of degree <= 2 is (1+X)^a Q^b.
    shapes = defaultdict(list)
    quad_power = 1
    for b in range(N//2+1):
        mask = quad_power
        for a in range(N-2*b+1):
            weight = mask.bit_count()
            if weight <= 4:
                shapes[weight].append(mask)
            mask ^= mask << 1
        quad_power ^= (quad_power << 1) ^ (quad_power << 2)

    supports = set()
    for weight in (1, 2):
        for left in shapes[weight]:
            for right in shapes[5-weight]:
                d, e = left.bit_length()-1, right.bit_length()-1
                # Anchor the two endpoints, allowing one side to span the entire support.
                if d == N:
                    offsets = range(N-e+1)
                elif e == N:
                    offsets = range(d-N, 1)
                else:
                    offsets = (N-e, d-N)
                for offset in offsets:
                    a, b = left << max(0, -offset), right << max(0, offset)
                    if a & b:
                        continue
                    interior = (a | b) ^ (1 << N) ^ 1
                    taps = []
                    while interior:
                        bit = interior & -interior
                        taps.append(bit.bit_length()-1)
                        interior ^= bit
                    supports.add(tuple(taps))
    return supports


def partition_forms():
    # A reciprocal three-term side is an arithmetic progression. A reciprocal
    # four-term side has the sums of the outside and inside exponents equal.
    for size, coefficients in ((3, (1, -2, 1)), (4, (1, -1, -1, 1))):
        for positions in combinations(range(5), size):
            row = [0]*5
            for position, coefficient in zip(positions, coefficients):
                row[position] = coefficient
            yield positions, row


def intersections(first, second):
    for i, j in combinations((1, 2, 3), 2):
        det = first[i]*second[j] - first[j]*second[i]
        if not det:
            continue
        k = 6-i-j
        for t in range(1, N):
            a, b = -N*first[4]-t*first[k], -N*second[4]-t*second[k]
            p, q = a*second[j]-b*first[j], b*first[i]-a*second[i]
            if p % det or q % det:
                continue
            support = [0, 0, 0, 0, N]
            support[i], support[j], support[k] = p//det, q//det, t
            if 0 < support[1] < support[2] < support[3] < N:
                yield tuple(support[1:4])
        return
    # Proportional interior rows would need proportional endpoint coefficients
    # for consistency. Their sums are zero and the original forms are distinct.


def translate_rows(taps, forms):
    support = (0, *taps, N)
    rows = []
    for positions, form in forms:
        if sum(x*y for x, y in zip(support, form)):
            continue
        side = [support[i] for i in positions]
        rest = [s for i, s in enumerate(support) if i not in positions]
        if len(side) == 3:
            h, k = side[1]-side[0], rest[1]-rest[0]
            terms = ((3*h, 1), (h, -1), (k, -1))
        else:
            terms = ((side[1]-side[0], 1), (side[2]-side[0], 1))
        row = Counter()
        for exponent, sign in terms:
            power = exponent & -exponent
            row[exponent//power] += sign*power
        rows.append(row)
    labels = sorted(set().union(*rows))
    return labels, Matrix([[row[j] for j in labels] for row in rows])


def check_free_coordinates(taps, forms):
    labels, rows = translate_rows(taps, forms)
    vectors = []
    for v in rows.nullspace():
        scale = lcm(*(int(x.q) for x in v))
        vectors.append([int(scale*x) for x in v])
    for i in range(len(labels)):
        if not any(gcd(v[i], GROUP) == 1 for v in vectors):
            raise ArithmeticError(f"missing a free direction modulo the full group order at {taps}")
    return len(labels), rows.rank()


def main():
    small = small_factors()
    smooth = quadratic_smooth_supports()
    hits = sorted(t for t in smooth if irreducible_candidate(t, small))
    if len(smooth) != 770 or hits != [(2, 4, 1101), (128, 1225, 1227)]:
        raise ArithmeticError("quadratic factor census failed")

    forms = list(partition_forms())
    supports = set()
    for (_, a), (_, b) in combinations(forms, 2):
        supports.update(intersections(a, b))
    hits = sorted(t for t in supports if irreducible_candidate(t, small))
    classes = [t for t in hits if t <= tuple(N-i for i in reversed(t))]
    expected = [(62, 93, 124), (67, 134, 648), (163, 533, 1066),
                (166, 249, 332), (310, 609, 919), (313, 626, 771)]
    if len(supports) != 5936 or len(hits) != 12 or classes != expected:
        raise ArithmeticError("multiple-partition census failed")
    for taps in hits:
        labels, rank = check_free_coordinates(taps, forms)
        if taps in classes:
            print(f"{taps}: {labels} translated powers, rank {rank}")

    f = modulus(N, (2, 4, 1101))
    check_known_order(f)
    if (X**1101*(1+X)**128 + (1+X+X*X)**2) % f != 0 or gcd(1101, GROUP) != 1:
        raise ArithmeticError("quadratic product or equal-order test failed")
    f = modulus(N, (310, 609, 919))
    check_known_order(f)
    x, y = X**310, X**609
    pairs = (((1+x)*(1+y), X**1229), ((1+x)*(1+x*y), y),
             (1+y, X**620*(1+x*y)), (y*(1+x**3), (1+x)**2))
    if any((a+b) % f != 0 for a, b in pairs) or gcd(620, GROUP) != 1:
        raise ArithmeticError("translate product or equal-order test failed")
    print("Verified both censuses, both order projections and all product identities.")


if __name__ == "__main__":
    main()
