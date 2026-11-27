"""Independent binary-integer census for a degree-11 scalar of exact order 2047."""

import argparse
from itertools import combinations
from math import gcd


def scalar_residues(n):
    order = 2047
    endpoint = n % order
    if endpoint == 0:
        raise ValueError("the two endpoint residues must be distinct")
    # Multiply by X modulo X^11+X^2+1, recording the logarithm of each residue.
    powers, logs = [], {}
    value = 1
    for exponent in range(order):
        if not value or value in logs:
            raise ArithmeticError("the proposed generator does not have order 2047")
        powers.append(value)
        logs[value] = exponent
        value <<= 1
        if value >> 11:
            value ^= (1 << 11) | 5
    if value != 1:
        raise ArithmeticError("the generator did not return to one")

    # For alpha = X^i, solve alpha^v = 1 + alpha^n for the third residue v.
    return {pow(i, -1, order) * logs[1 ^ powers[i*endpoint % order]] % order
            for i in range(1, order) if gcd(i, order) == 1}


def trinomial(pair, singleton):
    terms = [*pair, singleton]
    low = min(terms)
    return sum(1 << (e-low) for e in terms)


def gcd_degree(a, b):
    while b:
        offset = a.bit_length() - b.bit_length()
        if offset < 0:
            a, b = b, a
        else:
            a ^= b << offset
    return a.bit_length() - 1


def check_pairs_2047(q):
    n, order = 11*q, 2047
    thirds = scalar_residues(n)
    count, maximum = 0, 0
    for third in thirds:
        residues = (0, n % order, third)
        interior = sorted(e for r in residues for e in range(r, n+1, order) if 0 < e < n)
        for middle in combinations(interior, 3):
            support = [0, *middle, n]
            classes = [[e for e in support if e % order == r] for r in residues]
            if sorted(map(len, classes)) != [1, 2, 2]:
                continue
            count += 1
            singleton = next(c[0] for c in classes if len(c) == 1)
            a, b = (trinomial(c, singleton) for c in classes if len(c) == 2)
            maximum = max(maximum, gcd_degree(a, b))
    if maximum >= q:
        raise ArithmeticError(f"a common factor of degree {q} requires a field test")
    return [len(thirds), count, maximum, 0, 0]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("q", type=int, choices=(997, 1361))
    args = parser.parse_args()
    print(*check_pairs_2047(args.q))
