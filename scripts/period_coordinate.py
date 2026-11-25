"""Construct and check a Gauss period in either sparse field of degree 1229."""

import argparse
from itertools import chain

from check_factor_base import irreducible, modulus, polynomial


DEGREE = 1229
PRIME = 2 * DEGREE + 1
CANDIDATES = {"product": (27, 50, 77), "seroussi": (2, 6, 15)}


def frobenius_indices(n):
    """Index the nonzero residues modulo 2n+1 up to sign by powers of two."""
    p = 2*n + 1
    indices = {}
    for k in range(n):
        u = pow(2, k, p)
        if u in indices or p-u in indices:
            raise ValueError("the signed powers of two repeat early")
        indices[u] = indices[p-u] = k
    if len(indices) != p-1:
        raise ValueError("the signed powers of two do not cover the residues")
    return indices


def dickson_value(j, a, f):
    """Evaluate D_j(a) modulo f by maintaining D_i(a) and D_(i+1)(a)."""
    b, c = a*0, a
    for bit in bin(j)[2:]:
        odd = (b*c % f) + a
        if bit == "1":
            b, c = odd, c*c % f
        else:
            b, c = b*b % f, odd
    return b


def period_polynomial(n):
    """Return the square root of D_(2n+1)(T)/T by ordinary polynomial recurrence."""
    b, c = 0, 2
    for _ in range(2*n):
        b, c = c, (c << 1) ^ b
    mask = sum(((c >> (2*i+1)) & 1) << i for i in range(n+1))
    if sum(1 << (2*i+1) for i in range(n+1) if mask & (1 << i)) != c:
        raise ArithmeticError("D_(2n+1) did not have the expected odd powers")
    return polynomial(mask)


def coordinate(f):
    """Project (u+t+1)/(u+t) to the (2n+1)-torsion, starting with u=X and t²+t+1=0."""
    n = f.degree()
    frobenius_indices(n)
    p = 2*n + 1
    if n % 2 == 0 or (2**n + 1) % p or not irreducible(f):
        raise ValueError("expected an odd extension degree, p dividing 2^n+1, and a field")
    # The choices u and u+1 give inverse torus points with the same trace.
    for mask in chain((2,), range(4, 1 << n, 2)):
        u = polynomial(mask)
        g, inv, _ = (u*u+u+1).xgcd(f)
        if g != 1:
            raise ArithmeticError("the trace denominator has no inverse")
        a = dickson_value((2**n + 1)//p, inv % f, f)
        if a != 0:
            break
    else:
        raise ArithmeticError("no nonidentity prime-torsion projection")
    if dickson_value(p, a, f) != 0:
        raise ArithmeticError("the chosen trace failed the prime-torsion test")
    if period_polynomial(n).compose_mod(a, f) != 0:
        raise ArithmeticError("the independent minimal-polynomial check failed")
    return a


def mask_of(f):
    return sum(int(c) << i for i, c in enumerate(f))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", choices=CANDIDATES, nargs="?")
    args = parser.parse_args()
    for name in ([args.candidate] if args.candidate else CANDIDATES):
        a = coordinate(modulus(DEGREE, CANDIDATES[name]))
        print(f"{name} period mask = {mask_of(a):#x}")
