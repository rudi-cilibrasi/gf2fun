"""Classify sparse binary polynomials with a cubic right component.

The conic calculation exhausts finite graphs of binary digits without a degree
cutoff. FLINT checks the surviving field orders and the shifted trinomials.
"""

from collections import defaultdict, deque
from functools import cache
from math import gcd

from check_cubed_parity import X, polynomial
from check_power_orbit_collisions import root_order


def row_basis(rows):
    """Reduced binary row basis in a fixed pivot order."""
    pivots = {}
    for row in rows:
        while row:
            col = row.bit_length() - 1
            if col not in pivots:
                pivots[col] = row
                break
            row ^= pivots[col]
    for col in sorted(pivots):
        for higher in pivots:
            if higher > col and pivots[higher] >> col & 1:
                pivots[higher] ^= pivots[col]
    return tuple(pivots[col] for col in sorted(pivots))


def conic_supports(low, size):
    """Read bits of size sorted positive exponents, least significant first."""
    columns = 2*size
    mask = (1 << columns) - 1
    # Each exponent has two columns, one for each rational point. Multiplying
    # by the common denominator gives either D or the corresponding numerator.
    numerators = (1, 0b101) if low == 1 else (0b110, 0b010)
    multipliers = []
    for digit in range(1 << size):
        polynomials = [numerators[j % 2] if digit >> (j//2) & 1 else 0b111
                       for j in range(columns)]
        multipliers.append(tuple(sum(((v >> k) & 1) << j for j, v in enumerate(polynomials))
                                 for k in range(3)))

    @cache
    def transition(rows, digit):
        p, q, r = multipliers[digit]
        split = []
        for row in rows:
            a, b = row & mask, row >> columns
            # (a+bt)(p+qt+rt²) = even(t)² + t*odd(t)², columnwise.
            split.append((a & p) | (((a & r) ^ (b & q)) << columns))
            split.append(((a & q) ^ (b & p)) | ((b & r) << columns))
        reduced = row_basis(split)
        # Every remaining rational power is nonzero.
        if any(((row & mask) | (row >> columns)).bit_count() == 1 for row in reduced):
            return None
        return reduced

    @cache
    def accepts_zero_exponents(rows):
        return all((row & mask).bit_count() % 2 == 0 and (row >> columns).bit_count() % 2 == 0
                   for row in rows)

    # The first exponent is capped at low+1. The current binary place is
    # capped at four, which suffices for low = 1 or 2. Parity -1 marks the start.
    start = ((mask,), 0, 0, 1, -1)
    identifiers = {start: 0}
    states = [start]
    edges, reverse, terminal = [], defaultdict(list), defaultdict(list)
    all_less = (1 << (size-1)) - 1
    for src, (rows, less, first, place, parity) in enumerate(states):
        outgoing = []
        for digit in range(1 << size):
            if parity == -1 and digit == 0:  # a square has no odd exponent
                continue
            top_bit = digit >> (size-1)
            odd_degree = top_bit if parity == -1 else parity
            new_first = min(low+1, first + place*(digit & 1))
            if odd_degree and (new_first > low or (place >= 4 and new_first < low)):
                continue
            next_rows = transition(rows, digit)
            if next_rows is None:
                continue
            # At the highest differing bit the larger exponent has a one.
            right = digit >> 1
            differs = (right ^ digit) & all_less
            new_less = (less & ~differs) | (right & differs)
            target = (next_rows, new_less, new_first, min(4, 2*place), odd_degree)
            if target not in identifiers:
                identifiers[target] = len(states)
                states.append(target)
            dst = identifiers[target]
            outgoing.append((digit, dst))
            reverse[dst].append(src)
            trace_matches = new_first == low if odd_degree else new_first > low
            if top_bit and new_less == all_less and trace_matches and accepts_zero_exponents(next_rows):
                terminal[src].append(digit)
        edges.append(outgoing)

    live = set(terminal)
    queue = deque(live)
    while queue:
        for previous in reverse[queue.popleft()]:
            if previous not in live:
                live.add(previous)
                queue.append(previous)

    supports = []
    active = set()

    def read_paths(src, exponents, bit):
        if src in active:
            raise ArithmeticError("an accepting binary word can traverse a cycle")
        active.add(src)

        def append(digit):
            return tuple(e + (((digit >> j) & 1) << bit) for j, e in enumerate(exponents))

        supports.extend(append(digit) for digit in terminal[src])
        for digit, dst in edges[src]:
            if dst in live:
                read_paths(dst, append(digit), bit+1)
        active.remove(src)

    if 0 in live:
        read_paths(0, (0,)*size, 0)
    print(f"Inner X³+X^{low}, {size+1} terms: {len(states)} reachable states, "
          f"{len(live)} can finish, accepted supports {len(supports)}.")
    return set(supports)


# Positive exponents paired with the binary mask of the outer polynomial.
OUTERS = {
    1: {(1, 3): 0x3, (1, 5, 7, 9): 0xb, (1, 9, 13, 15): 0x2b},
    2: {(2, 3): 0x3, (4, 7, 9, 12): 0x1d, (6, 7, 9, 12): 0x19},
}


def check_conics():
    for low, outers in OUTERS.items():
        found = conic_supports(low, 2) | conic_supports(low, 4)
        if found != set(outers):
            raise ArithmeticError(f"unexpected supports for X³+X^{low}: {found}")
        h = X**3 + X**low
        for exponents, mask in outers.items():
            f = polynomial((0, *exponents))
            outer = polynomial(j for j in range(mask.bit_length()) if mask >> j & 1)
            if outer(h) != f:
                raise ArithmeticError("incorrect composition")
            if outer(1) == 0 and outer.degree() > 1:
                if f % (h+1) or f.is_irreducible():
                    raise ArithmeticError("expected cubic factor")
            elif not f.is_irreducible() or root_order(f) != 2**f.degree()-1:
                raise ArithmeticError("incorrect primitive order")
            else:
                print(f"  {exponents}: primitive of order {2**f.degree()-1}.")


def check_translated_dilations():
    """Classify the three families through 262145, with one unresolved order."""
    limit = (1 << 18) + 1
    divisors = [polynomial(j for j in range(mask.bit_length()) if mask >> j & 1)
                for mask in (0x7, 0xd, 0x1162300f)]
    unresolved = []
    orders = {6: (63, 9), 12: (455, 45), 18: (87381, 189),
              20: (1048575, 75), 66: (2**66-1, 12582909)}
    found = {}
    for j in range(1, limit.bit_length()):
        for k in range(1, limit.bit_length()):
            b, c = 1 << j, 1 << k
            n = b+c
            if n > limit or min(j, k) > 2 or (k//gcd(j, k)) % 2:
                continue
            d = gcd(b+1, c-1)
            if d != (1 << gcd(j, k)) + 1:
                raise ArithmeticError("unexpected dilation")
            if n > 4097:
                m = n//d
                power = m if b+1 == d else m-1
                if gcd(power, pow(2, m, power)-1) > 1:
                    continue
                # Test each small proper factor of the required base trinomial.
                if any(q.degree() < m and (X.pow_mod(m, q) + X + 1) % q == 0 for q in divisors):
                    continue
                unresolved.append(n)
                if n == 4098 and not polynomial((0, 1, c, b+1, n)).is_irreducible():
                    raise ArithmeticError("the degree-4098 candidate is reducible")
                continue
            f = polynomial((0, 1, c, b+1, n))
            translated = polynomial((0, b+1, n))
            if f(X+1) != translated:
                raise ArithmeticError("translation mismatch")
            if not f.is_irreducible():
                continue
            if n in found or n not in orders:
                raise ArithmeticError(f"unexpected irreducible pentanomial in degree {n}")
            found[n] = root_order(f), root_order(translated)
    if unresolved != [4098]:
        raise ArithmeticError(f"unexpected unresolved orders: {unresolved}")
    print(f"Through {limit}, only degree 4098 remains unresolved among proper translated dilations.")
    if found != orders:
        raise ArithmeticError(f"incorrect translated-root or original-root orders: {found}")
    for n, (original, shifted) in sorted(found.items()):
        print(f"Degree {n}: root order {original}, translated-root order {shifted}.")


if __name__ == "__main__":
    check_conics()
    check_translated_dilations()
