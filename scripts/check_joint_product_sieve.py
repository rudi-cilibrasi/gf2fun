"""Check the simultaneous factor-count and reciprocal-root construction over GF(2)."""

import argparse
from math import gcd, lcm

from flint import fmpz_poly, nmod_poly


X = nmod_poly([0, 1], 2)
Y = fmpz_poly([0, 1])


def factor_degrees(f):
    return sorted((p.degree(), e) for p, e in f.factor()[1])


def signed_resultants(n, q, w):
    """Compute both integer resultants modulo eight, reducing H in a small quotient."""
    s, v = q - 1, n - (q + 1) * w
    y = nmod_poly([0, 1], 8)
    c = y**s + 1
    a = y**(q+1) + c
    residues = []
    for sign in (1, -1):
        j = y**q - sign*c
        h = (y.pow_mod(v, j) * a.pow_mod(w, j) + c.pow_mod(w, j)) % j
        lift = fmpz_poly([int(k) for k in h])
        residues.append(int((Y**q - sign*(Y**s+1)).resultant(lift)) % 8)
    return residues


def check(n, s, w, even_case):
    u, v, g = s*w, n-(s+2)*w, n+2*w
    if not 0 < u < v < n-u or gcd(w, n) != 1:
        raise ValueError(f"invalid sample {(n, s, w)}")
    f = X**n + (1+X**u)*(1+X**v)
    degrees = factor_degrees(f)
    if len(degrees) % 2 != 1 or any(e != 1 for _, e in degrees):
        raise ArithmeticError(f"squarefreeness or factor parity failed at {(n, s, w)}")
    b, period = 0, 1
    while s % lcm(period, 2**(b+1)-1) == 0:
        b += 1
        period = lcm(period, 2**b-1)
    if degrees[0][0] <= b:
        raise ArithmeticError(f"small-factor sieve failed at {(n, s, w)}")
    t = X**(s+2) + (1+X**s)*(1+X**(s+4))
    shared = t.gcd(X.pow_mod(g, t)+1)
    # The coprime w-th power permutes the g-th roots, also when g is even.
    free = f.gcd(f.reverse()) == 1
    if free != (shared == 1):
        raise ArithmeticError(f"reciprocal obstruction disagrees at {(n, s, w)}")
    if even_case:
        q = s+1
        c, a = X**s + 1, X**(q+1) + X**s + 1
        if degrees != factor_degrees(X**v*a**w+c**w):
            raise ArithmeticError(f"root transport failed at {(n, s, w)}")
        left, right = signed_resultants(n, q, w)
        if left*right % 8 != 5:
            raise ArithmeticError(f"lifted resultant failed at {(n, s, w)}")
    if n <= 112:
        lift = Y**n + (1+Y**u)*(1+Y**v)
        if int(lift.discriminant()) % 8 != (5 if even_case else 1):
            raise ArithmeticError(f"integer discriminant failed at {(n, s, w)}")
    return free, len(degrees) == 1


def main(through):
    odd = even = free_odd = free_even = 0
    for n in range(3, through+1, 2):
        if n % 8 not in (3, 5):
            continue
        for s in (1, 3, 5, 7, 15, 21):
            for w in range(1, n//(2*s+2)+1, 2):
                if 3*s*w >= n or (n-(s+2)*w) % 8 or gcd(w, n) != 1:
                    continue
                free, _ = check(n, s, w, False)
                free_odd += free
                odd += 1
    for q in (8, 16, 32, 64):
        for k in ((1, 9) if q <= 16 else (1,)):
            for w in (1, 3, 5, 7, 9, 15):
                n = 2*q*w + 1 + k*(q*q-1)
                if gcd(n, w) != 1:
                    continue
                free, _ = check(n, q-1, w, True)
                free_even += free
                even += 1
    for s, w in ((1, 295), (17, 15), (363, 1)):
        if check(1229, s, w, False) != (True, True):
            raise ArithmeticError("invalid degree-1229 example")
    print(f"Verified odd factor counts for {odd} odd-degree and {even} even-degree samples. "
          f"The reciprocal test passes for {free_odd} and {free_even}, respectively. "
          "Verified three irreducible members at degree 1229.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=256, help="odd-degree sample limit")
    args = parser.parse_args()
    if args.through < 5:
        parser.error("expected an odd-degree limit of at least five")
    main(args.through)
