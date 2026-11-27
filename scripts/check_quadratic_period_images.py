"""Classify sparse primitive rational images of degree at most two of binary optimal bases."""

from collections import deque
from functools import cache, reduce
from itertools import permutations
from operator import xor

from sympy import isprime, n_order

from check_cyclic_trinomial_parity import inverse_mod
from check_gauss_period_weights import full_period_orbit, order
from make_witnesses import gcd, mask_product, remainder
from period_fibres import minimal_polynomial


multiply = cache(mask_product)
CUTOFF = 5


def trim(rows):
    rows = list(rows)
    while rows and not rows[-1]:
        rows.pop()
    return tuple(rows)


@cache
def product(left, right):
    """Bivariate polynomial product, with coefficients in packed binary X."""
    if not left or not right:
        return ()
    result = [0] * (len(left)+len(right)-1)
    for i, row in enumerate(left):
        for j, other in enumerate(right):
            result[i+j] ^= multiply(row, other)
    return trim(result)


def initial_resultant(source, quadratic):
    """Sylvester determinant for source degrees zero through three."""
    n = source.bit_length()-1
    bits = [(source >> j) & 1 for j in range(n+1)]
    matrix = [bits+[0], [0]+bits]
    for i in range(n):
        matrix.append([0]*i + list(quadratic) + [0]*(n-1-i))
    result = 0
    for permutation in permutations(range(n+2)):
        term = 1
        for row, column in enumerate(permutation):
            term = multiply(term, matrix[row][column])
        result ^= term
    return result


@cache
def parity_part(mask, parity):
    return sum(((mask >> (2*i+parity)) & 1) << i for i in range((mask.bit_length()+1)//2))


def cartier_transitions(numerator, denominator):
    """Enumerate numerators over the fixed denominator under both Cartier operators."""
    states = [numerator]
    indices = {numerator: 0}
    transitions = []
    for state in states:
        expanded = product(state, denominator)
        children = []
        for digit in (0, 1):
            pair = []
            for parity in (0, 1):
                child = trim(parity_part(row, parity) for row in expanded[digit::2])
                if child not in indices:
                    indices[child] = len(states)
                    states.append(child)
                pair.append(indices[child])
            children.append(pair)
        transitions.append(children)
    base = tuple(min(CUTOFF+1, s[0].bit_count()) if s else 0 for s in states)
    return base, transitions


def sparse_indices(numerator, denominator, type_one):
    """Exhaust all productive binary paths, rejecting a cycle if an accepting word can follow it."""
    base, transitions = cartier_transitions(numerator, denominator)

    def step(values, digit):
        return tuple(min(CUTOFF+1, values[row[digit][0]]+values[row[digit][1]])
                     for row in transitions)

    def successor(state, digit):
        values, residue = state
        return step(values, digit), (2*residue+digit) % 8 if type_one else 0

    initial = successor((base, 0), 1)
    states = [initial]
    ids = {initial: 0}
    reverse = [[]]
    edges = []
    for i, state in enumerate(states):
        children = []
        for digit in (0, 1):
            child = successor(state, digit)
            if child not in ids:
                ids[child] = len(states)
                states.append(child)
                reverse.append([])
            dest = ids[child]
            children.append(dest)
            reverse[dest].append(i)
        edges.append(children)

    # A type-I prime conductor n+1 has 2 as a quadratic nonresidue.
    accepting = {i for i, (v, residue) in enumerate(states)
                 if v[0] <= CUTOFF and (not type_one or residue in (2, 4))}
    live = set(accepting)
    queue = deque(accepting)
    while queue:
        for parent in reverse[queue.popleft()]:
            if parent not in live:
                live.add(parent)
                queue.append(parent)

    def visit(i, n, ancestors):
        if i not in live:
            return
        if i in ancestors:
            raise ArithmeticError("a productive cycle gives infinitely many indices")
        if i in accepting:
            yield n
        for digit, child in enumerate(edges[i]):
            yield from visit(child, 2*n+digit, ancestors | {i})

    return set(visit(0, 1, set())), len(states)


def polynomial_family(top, bottom, type_one):
    # The quadratic in T is a*T^2 + b*T + c = top(T) + X*bottom(T).
    quadratic = tuple(((top >> j) & 1) ^ (((bottom >> j) & 1) << 1) for j in range(3))
    c, b, a = quadratic
    if type_one:
        denominator = product(product((1, a), (1, c)), (1, b, multiply(a, c)))
        sources = (1, 3, 7, 15)
    else:
        a2 = multiply(a, a)
        denominator = (1, c, multiply(b, b), multiply(a2, c), multiply(a2, a2))
        sources = (1, 3, 7, 13)
    starts = tuple(initial_resultant(f, quadratic) for f in sources)
    numerator = trim(product(denominator, starts)[:4])
    return starts, denominator, numerator


def resultants(starts, denominator, last):
    values = list(starts)
    for n in range(len(starts), last+1):
        values.append(reduce(xor, (multiply(c, values[n-i])
                                   for i, c in enumerate(denominator[1:], 1)), 0))
    return values


def source_mask(n, type_one):
    if type_one:
        return (1 << (n+1))-1
    previous, current = 1, 3
    for _ in range(1, n):
        previous, current = current, (current << 1) ^ previous
    return current


def field_image(n, type_one, top, bottom, resultant):
    source = source_mask(n, type_one)
    reciprocal = inverse_mod(remainder(bottom, source), source)
    if reciprocal is None:
        if resultant != 1:
            raise ArithmeticError("unexpected resultant at infinity")
        return None
    value = remainder(multiply(top, reciprocal), source)
    minimal = minimal_polynomial(value, source)
    degree = minimal.bit_length()-1
    if degree == n:
        expected = minimal
    elif 2*degree == n:
        expected = multiply(minimal, minimal)
    else:
        raise ArithmeticError("index of the rational value exceeds two")
    if expected != resultant:
        raise ArithmeticError("field evaluation disagrees with the symbolic resultant")
    return degree, minimal


def classify(type_one):
    candidates = set()
    primitive = set()
    full_sparse = set()
    proper_images = set()
    maximum_states = 0
    examples = {23: 0x828009, 30: 0x40002043}
    for top in range(1, 8):
        for bottom in range(1, 8):
            if max(top, bottom) < 4 or gcd(top, bottom) != 1:
                continue
            starts, denominator, numerator = polynomial_family(top, bottom, type_one)
            indices, count = sparse_indices(numerator, denominator, type_one)
            maximum_states = max(maximum_states, count)
            # Independent direct stepping checks every degree through the largest survivor.
            limit = max(512, max(indices, default=0))
            polys = resultants(starts, denominator, limit)
            direct = {n for n in range(1, limit+1)
                      if polys[n].bit_count() <= CUTOFF and (not type_one or n % 8 in (2, 4))}
            if direct != indices:
                raise ArithmeticError("resultant recurrence disagrees with the automaton")
            candidates.update(indices)
            for n in sorted(indices):
                if n <= 1:
                    continue
                if type_one:
                    if not isprime(n+1) or n_order(2, n+1) != n:
                        continue
                elif not full_period_orbit(n):
                    continue
                image = field_image(n, type_one, top, bottom, polys[n])
                if image is None:
                    continue
                degree, minimal = image
                if degree == n:
                    full_sparse.add(n)
                if degree > 1:
                    actual = order(minimal, degree)
                    if actual == (1 << degree)-1:
                        primitive.add(degree)
                    else:
                        proper_images.add((degree, actual))
                if not type_one and top == 3 and bottom == 4 and n in examples:
                    if degree != n or minimal != examples[n] or order(minimal, n) != (1 << n)-1:
                        raise ArithmeticError("incorrect quadratic witness")
    return candidates, full_sparse, primitive, proper_images, maximum_states


def main():
    for type_one in (True, False):
        indices, full, primitive, proper, count = classify(type_one)
        expected_full = {2, 4, 10, 12} if type_one else {2, 3, 5, 6, 9, 11, 14, 23, 30}
        expected_primitive = {2, 4, 5, 6, 9} if type_one else {2, 3, 5, 6, 9, 11, 23, 30}
        if (max(indices) != (26 if type_one else 512) or full != expected_full
                or primitive != expected_primitive or (not type_one and (14, 5461) not in proper)):
            raise ArithmeticError("unexpected surviving degrees or orders")
        name = "I" if type_one else "II"
        print(f"Type {name}, 24 maps, at most {count} states. Candidate indices {sorted(indices)}.")
        print(f"Full-degree sparse images {sorted(full)}. Primitive target degrees {sorted(primitive)}.")


if __name__ == "__main__":
    main()
