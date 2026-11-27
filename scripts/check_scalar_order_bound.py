"""Find every possible rank-two scalar for all prime partners of a given smaller prime."""

import argparse
from math import comb, isqrt


def primes_through(limit):
    prime = bytearray([1]) * (limit + 1)
    prime[:2] = bytes(2)
    for d in range(2, isqrt(limit) + 1):
        if prime[d]:
            prime[d*d::d] = bytes((limit - d*d)//d + 1)
    return (i for i in range(3, limit + 1, 2) if prime[i])


def gcd_poly(a, b):
    while b:
        while a.bit_length() >= b.bit_length():
            a ^= b << (a.bit_length() - b.bit_length())
        a, b = b, a
    return a


def translated_power(m):
    """Coefficients of (X+1)^m, packed as bits."""
    value = 1
    while m:
        bit = m & -m
        value ^= value << bit
        m -= bit
    return value


def remainder(a, b):
    while a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def square_poly(a):
    # In characteristic two the two nibbles in each byte square independently.
    return int.from_bytes(b''.join(SQUARE[c] for c in a.to_bytes((a.bit_length()+7)//8, 'little')), 'little')


SQUARE = [sum(((c >> j) & 1) << (2*j) for j in range(8)).to_bytes(2, 'little') for c in range(256)]


def pow_poly(base, e, divisor):
    # Only the two bases X and X+1 are used.
    value = 1
    for digit in bin(e)[2:]:
        value = remainder(square_poly(value), divisor)
        if digit == '1':
            value = remainder((value << 1) ^ (value if base == 3 else 0), divisor)
    return value


def plane_degree(p, h):
    """Degree of gcd(X^h+1,(1+X)^h+1) using two short Frobenius identities."""
    relations = set()
    residue = 1
    for _ in range(p):
        for t in (residue, residue-h):
            t //= abs(t) & -abs(t)
            if t != 1:
                relations.add(t)
        residue = 2*residue % h
    if residue != 1:
        raise ValueError("incorrect Frobenius period")
    g = 0
    for t in sorted(relations, key=lambda t: (abs(t) if t > 0 else 2*abs(t), t))[:2]:
        base = translated_power(abs(t))
        if t > 0:
            f = base ^ (1 << t) ^ 1
        else:
            f = base ^ (base << -t) ^ (1 << -t)
        if not f:
            raise ArithmeticError("zero auxiliary polynomial")
        g = gcd_poly(g, f)
    if not g:
        raise ArithmeticError("missing Frobenius equation")
    for base in (2, 3):
        if g == 1:
            break
        g = gcd_poly(g, pow_poly(base, h, g) ^ 1)
    return g.bit_length() - 1


def possible_scalars(p):
    # Every prime divisor of the scalar is 1 mod 2p, and (2p+1)^2 exceeds the upper bound.
    first = (3*p*p - 4 + 8*p-1) // (8*p)
    last = (12*p*p - 6) // (10*p)
    for k in range(first, last+1):
        h = 2*p*k + 1
        if pow(2, p, h) == 1:
            yield h


def ball_size(k):
    return sum(comb(3, i) * comb(3-i, j) * comb(k, i) * comb(k, j)
               for i in range(4) for j in range(4-i))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=10000, help='largest smaller prime to examine')
    parser.add_argument('--list', action='store_true', help='print all scalar candidates and gcd degrees')
    args = parser.parse_args()
    if args.limit < 3:
        parser.error('the smaller prime must be at least three')
    scanned = candidates = 0
    survivors = []
    for p in primes_through(args.limit):
        scanned += 1
        if 12*ball_size((p-1)//2) != 5*p**3 + 7*p:
            raise ArithmeticError('signed lattice count disagrees with its formula')
        for h in possible_scalars(p):
            candidates += 1
            degree = plane_degree(p, h)
            if args.list:
                print(p, h, degree)
            if degree:
                survivors.append((p,h,degree))
    if args.limit == 10000 and (scanned, candidates, survivors) != (1228, 96, [(3,7,6),(5,31,30)]):
        raise ArithmeticError(f'unexpected census: {scanned}, {candidates}, {survivors}')
    print(f'{scanned} odd primes, {candidates} scalar orders, surviving (p, order, gcd degree): {survivors}')


if __name__ == '__main__':
    main()
