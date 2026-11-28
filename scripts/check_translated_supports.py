"""Classify supports of binary trinomials and pentanomials whose unit translates also have at most five terms."""

import argparse
from collections import Counter
from itertools import combinations, permutations


def translate(rows):
    """Expand every product of variables Y_i+1, cancelling equal subsets."""
    shifted = set()
    for term in rows:
        subset = term
        while True:
            shifted.symmetric_difference_update((subset,))
            if subset == 0:
                break
            subset = (subset-1) & term
    return tuple(sorted(shifted))


def compress(rows):
    universe = 0
    for row in rows:
        universe |= row
    bits = [1 << i for i in range(universe.bit_length()) if universe >> i & 1]
    return tuple(sum(1 << i for i, bit in enumerate(bits) if row & bit) for row in rows)


def substitute(rows, positions):
    return tuple(sorted(sum(1 << k for i, k in enumerate(positions) if row >> i & 1)
                        for row in rows))


def canonical(rows):
    rows = compress(rows)
    variables = max(rows).bit_length()
    return min(substitute(rows, order) for order in permutations(range(variables)))


def incidence_supports(size, limit):
    """A variable belongs to a nonempty subset of the indexed monomials."""
    def visit(pattern, rows, used):
        if pattern == 0:
            if 0 not in rows and len(set(rows)) == size:
                yield rows
            return
        members = [i for i in range(size) if pattern >> i & 1]
        remaining = min(limit - rows[i].bit_count() for i in members)
        for count in range(remaining+1):
            bits = ((1 << count)-1) << used
            child = list(rows)
            for i in members:
                child[i] |= bits
            yield from visit(pattern-1, tuple(child), used+count)

    return visit((1 << size)-1, (0,)*size, 0)


def catalogue():
    result = set()
    for size in (2, 4):
        limit = size.bit_length()-1 + 2
        for rows in incidence_supports(size, limit):
            shifted = translate(rows)
            if len(shifted) not in (2, 4):
                continue
            # The bit positions in 'rows' are consecutive and all are used.
            if max(rows).bit_length() > 4:
                raise ArithmeticError("a sparse translated pair uses more than four binary positions")
            result.add(canonical(rows))

    # Independently reconstruct all surviving types from the nonconstant
    # multilinear monomials in four labelled variables.
    small = {canonical(rows) for size in (2, 4) for rows in combinations(range(1, 16), size)
             if len(translate(rows)) in (2, 4)}
    if small != result:
        raise ArithmeticError("the two classifications disagree")
    counts = Counter((len(r)+1, len(translate(r))+1, max(r).bit_length()) for r in result)
    expected = {(3, 3, 2): 2, (3, 5, 3): 3, (5, 3, 3): 3, (5, 5, 3): 6, (5, 5, 4): 14}
    if counts != expected:
        raise ArithmeticError("incorrect count of translated support types")
    return sorted(result, key=lambda r: (len(r), r))


def degree_supports(n, types):
    required = {k for k in range(n.bit_length()) if n >> k & 1}
    optional = sorted(set(range(n.bit_length())) - required)
    supports = set()
    for rows in types:
        extra = max(rows).bit_length() - len(required)
        if extra < 0:
            continue
        for chosen in combinations(optional, extra):
            for positions in permutations((*sorted(required), *chosen)):
                support = substitute(rows, positions)
                if support[-1] == n:
                    supports.add(support)
    return sorted(supports, key=lambda s: (len(s), s))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree", type=int, help="list every eligible support in this degree")
    args = parser.parse_args()
    types = catalogue()
    if args.degree is None:
        print("nonconstant_monomial_masks -> translated_masks")
        for rows in types:
            print(rows, "->", translate(rows))
    else:
        if args.degree < 2:
            parser.error("use a degree of at least two")
        supports = degree_supports(args.degree, types)
        for rows in supports:
            print((0, *rows), "->", (0, *translate(rows)))
        print(f"{len(supports)} supports in degree {args.degree}.")


if __name__ == "__main__":
    main()
