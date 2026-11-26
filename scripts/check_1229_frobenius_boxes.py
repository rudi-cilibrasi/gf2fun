"""Find the smallest bidegrees of the five original terms after a power change of root.

Run with uv run --no-project --with numpy --with sympy --with python-flint==0.9.0
python scripts/check_1229_frobenius_boxes.py. Use --list to print the optimal square.
"""

import argparse
from collections import defaultdict
from math import gcd

import numpy as np

from check_1229_sparse_frobenius import support_table
from check_degree_1229 import GROUP, N, PRIMES, check_known_order
from check_factor_base import modulus, polynomial


# These three boxes cover the square of side 24 and every positive bidegree of area <= 45.
BOXES = ((24, 24), (1, 45), (45, 1))
CUBIC = (3, 410, 822)
QUADRATIC = (256, 461, 922)
BALANCED = (101, 614, 818)


def possible_frobenius_exponents():
    """Eliminate large Frobenius powers with a short relation modulo a common order divisor."""
    prime = PRIMES[-1]
    bound = N * max(max(box) for box in BOXES)
    exponents = []
    # Exchanging the coordinates replaces s by N-s. All search regions are symmetric.
    for s in range(N // 2 + 1):
        residue = pow(2, s, prime)
        if residue <= bound:
            exponents.append(s)
            continue
        # Consecutive Euclidean remainders have the form u = v * 2^s modulo prime.
        previous, u = prime, residue
        previous_v, v = 0, 1
        while u:
            if max(u, abs(v)) > bound and bound * (u + abs(v)) < prime:
                if gcd(u, v) != 1 or (u - v * residue) % prime:
                    raise ArithmeticError('invalid modular exclusion certificate')
                break
            quotient, remainder = divmod(previous, u)
            previous, u = u, remainder
            previous_v, v = v, previous_v - quotient*v
        else:
            raise ArithmeticError(f'no exclusion certificate found for s={s}')
    if exponents != list(range(16)):
        raise ArithmeticError(f'unexpected Frobenius exponents {exponents}')
    return exponents


def placements(width, height, q):
    """Generate increasing progressions with both endpoints in the box and three interior taps."""
    if q <= width:
        if width + q*height >= N:
            raise ArithmeticError('overlapping exponent rows require a separate enumeration')
        return
    for step in range(1, (width + q*height)//N + 1):
        for start in range(width + 1):
            end = start + N*step
            last_y, last_x = divmod(end, q)
            if last_x > width or last_y > height:
                continue
            taps = []
            for y in range(last_y + 1):
                for x in range(width + 1):
                    t = y*q + x - start
                    if 0 < t < N*step and t % step == 0:
                        taps.append(t // step)
            if len(taps) >= 3:
                yield step, start, last_y, taps


def census(exponents):
    # A reciprocal polynomial reverses the progression and reflects both axes.
    a, b, c = support_table()
    by_shape = defaultdict(set)
    eligible = np.zeros(N+1, dtype=bool)
    for width, height in BOXES:
        for s in exponents:
            q = 1 << s
            for step, start, last_y, taps in placements(width, height, q):
                if gcd(step, GROUP) != 1:
                    raise ArithmeticError('the power substitution must preserve the root order')
                eligible.fill(False)
                eligible[taps] = True
                for index in np.flatnonzero(eligible[a] & eligible[b] & eligible[c]):
                    triple = int(a[index]), int(b[index]), int(c[index])
                    xs = [(start + step*e) % q for e in (0, *triple, N)]
                    if min(xs) != 0:
                        continue  # The translation with minimum abscissa zero is also enumerated.
                    shape = tuple(sorted((max(xs), last_y)))
                    by_shape[shape].add(triple)
    return by_shape


def verify_field_example(taps, s, step, start, points):
    """Verify a displayed model at the root itself, including its known prime projections."""
    f = modulus(N, taps)
    x = polynomial(2)
    if x.pow_mod(1 << N, f) != x or f.gcd(x*x+x) != 1:
        raise ArithmeticError(f'reducible example {taps}')
    check_known_order(f)
    z = x.pow_mod(pow(step, -1, GROUP), f)
    y = z.pow_mod(1 << s, f)
    if z.pow_mod(step, f) != x or any(
            i + (j << s) != start + step*e for e, (i, j) in zip((0, *taps, N), points, strict=True)):
        raise ArithmeticError('failed to recover the original five monomials')
    relation = sum((z.pow_mod(i, f) * y.pow_mod(j, f) for i, j in points), polynomial(0))
    if relation % f != 0:
        raise ArithmeticError(f'Frobenius equation failed for {taps}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--list', action='store_true', help='print the twelve reciprocal representatives in the optimal square')
    args = parser.parse_args()
    by_shape = census(possible_frobenius_exponents())
    minima = {(a, b): len(taps) for (a, b), taps in by_shape.items()
              if not any(c <= a and d <= b and (c, d) != (a, b) for c, d in by_shape)}
    if minima != {(2, 24): 1, (3, 15): 1, (6, 14): 2, (8, 12): 2}:
        raise ArithmeticError(f'unexpected coordinatewise minima {minima}')
    for cost, minimum in ((sum, 18), (lambda pair: pair[0]*pair[1], 45)):
        optimal = {k: v for k, v in by_shape.items() if cost(k) <= minimum}
        if optimal != {(3, 15): {CUBIC}}:
            raise ArithmeticError(f'unexpected optimum at bound {minimum}')
    if by_shape[2, 24] != {QUADRATIC} or BALANCED not in by_shape[8, 12]:
        raise ArithmeticError('unexpected quadratic or balanced example')
    square = {k: len(v) for k, v in by_shape.items() if max(k) <= 12}
    optimal_taps = set().union(*(by_shape[k] for k in square))
    if square != {(8, 12): 2, (10, 12): 3, (11, 12): 6, (12, 12): 1} or len(optimal_taps) != 12:
        raise ArithmeticError(f'unexpected optimal square {square}')

    verify_field_example(CUBIC, 11, 5, 0, ((0, 0), (15, 0), (2, 1), (14, 2), (1, 3)))
    verify_field_example(BALANCED, 9, 5, 7, ((7, 0), (0, 1), (5, 6), (1, 8), (8, 12)))
    verify_field_example(QUADRATIC, 8, 5, 0, ((0, 0), (0, 5), (1, 9), (2, 18), (1, 24)))
    print('Minimum maximum degree 12, attained by 24 pentanomials in twelve reciprocal pairs.')
    print('Minimum sum 18 and minimum positive area 45, both attained only by taps (3,410,822) and their reciprocal.')
    print('Coordinatewise minimal bidegrees and reciprocal-pair counts:', sorted(minima.items()))
    if args.list:
        for shape in sorted(square):
            for a, b, c in sorted(by_shape[shape]):
                print(*shape, a, b, c, sep=',')


if __name__ == '__main__':
    main()
