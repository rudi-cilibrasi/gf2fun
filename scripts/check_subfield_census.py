"""Enumerate sparse roots in products of coprime prime-degree binary subfields."""

import argparse
import subprocess
from collections import defaultdict
from functools import cache
from itertools import combinations
from math import prod

from flint import fmpz

from check_factor_base import polynomial
from check_subfield_products import possible_plane_orders, small_orders
from period_coordinate import mask_of


X = polynomial(2)


def reverse_mask(mask):
    return int(f"{mask:b}"[::-1], 2)


def external_factors(limit, degrees, gp, ntl):
    """Read the factors of the canonical trinomials from PARI or NTL."""
    program = None
    if gp:
        program = f"needed={sorted(degrees)};\n" + (
            f"for(t=2,{limit},for(s=1,t\\2,if(t%2 || s%2,"
            "my(ff=factormod(x^t+x^s+1,2));for(i=1,matsize(ff)[1],"
            "my(fi=ff[i,1],d=poldegree(fi));if(setsearch(needed,d),"
            'print(t," ",s," ",d," ",subst(lift(fi),x,2)))))));\n'
            'print("finished");\nquit\n')
        command = [gp, "-q", "-f", "-s", "512M"]
    else:
        command = [ntl, str(limit), *map(str, sorted(degrees))]
    run = subprocess.run(command, input=program, capture_output=True, text=True, check=True)
    lines = run.stdout.splitlines()
    if run.stderr.strip() or not lines or lines.pop() != "finished":
        raise RuntimeError(f"factor enumeration failed: {run.stderr}")
    factors = defaultdict(list)
    for line in lines:
        t, s, d, mask = map(int, line.split())
        if not 0 < s <= t//2 or t > limit or d not in degrees or mask.bit_length() != d+1:
            raise ArithmeticError(f"invalid factor row: {line}")
        factors[t, s].append((d, mask))
    return factors


def trinomial_factors(limit, degrees, gp=None, ntl=None):
    """Index all relevant factors of 1+X^s+X^t, including squares and reciprocals."""
    by_degree = defaultdict(list)
    earlier = external_factors(limit, degrees, gp, ntl) if gp or ntl else {}
    for t in range(2, limit+1):
        for s in range(1, t):
            if 2*s > t:
                factors = [(d, reverse_mask(f)) for d, f in earlier[t, t-s]]
            elif t % 2 == s % 2 == 0:
                factors = earlier[t//2, s//2]
            elif gp or ntl:
                factors = earlier[t, s]
            else:
                factors = [(f.degree(), mask_of(f)) for f, _ in (X**t+X**s+1).factor()[1]
                           if f.degree() in degrees]
            earlier[t, s] = factors
            for d, f in factors:
                by_degree[d].append((t, s, f))
    return by_degree


@cache
def supports_plane(order, i, j):
    """Check the three projected powers of alpha, including alpha^0."""
    return len({0, i, j}) == 3 and (X**order+1).gcd(X**i+X**j+1).degree() > 0


@cache
def subgroup_factors(order, degree):
    return tuple(mask_of(f) for f, _ in (X**order+1).factor()[1] if f.degree() == degree)


def composed_minpoly(f, g):
    """First linear relation on (alpha beta)^i in the product of two power bases."""
    p, q = f.bit_length()-1, g.bit_length()-1
    n = p*q
    a = b = 1
    pivots = {}
    for i in range(n+1):
        vector = sum(b << (q*j) for j in range(p) if (a >> j) & 1)
        relation = 1 << i
        while vector:
            lead = vector.bit_length()-1
            if lead not in pivots:
                pivots[lead] = (vector, relation)
                break
            v, r = pivots[lead]
            vector ^= v
            relation ^= r
        if not vector:
            if i != n:
                raise ArithmeticError("product of coprime-degree roots has the wrong degree")
            return relation
        a <<= 1
        b <<= 1
        if a >> p:
            a ^= f
        if b >> q:
            b ^= g
    raise ArithmeticError("missing linear relation in the tensor product")


def exceptional_masks(n, p, q, order, trinomials):
    result = set()
    # This covers all 3,1,1 partitions since equal singleton sums force ord(beta) <= n.
    for other in small_orders(q, n):
        for f in subgroup_factors(order, p):
            for g in subgroup_factors(other, q):
                mask = composed_minpoly(f, g)
                if mask.bit_count() <= 5:
                    result.add(mask)

    # Translate the singleton in a 2,2,1 partition to exponent zero.
    pairs = defaultdict(set)
    for t, s, factor in trinomials:
        if t > n:
            break
        for i, j in ((s, t), (-s, t-s), (-t, s-t)):
            if (j-i) % order == 0:
                pairs[factor].add((i, j))
    for choices in pairs.values():
        for (i, j), (k, l) in combinations(choices, 2):
            support = {0, i, j, k, l}
            low = min(support)
            if len(support) == 5 and max(support)-low == n and supports_plane(order, i % order, k % order):
                result.add(sum(1 << (e-low) for e in support))
    return result


def census(limit, gp=None, ntl=None):
    primes = [p for p in range(3, limit//3+1, 2) if fmpz(p).is_prime()]
    degrees = sorted((p*q, p, q) for p, q in combinations(primes, 2) if p*q <= limit)
    options = {(u, v): possible_plane_orders(u, v)
               for _, p, q in degrees for u, v in ((p, q), (q, p))}
    factors = trinomial_factors(limit, {v for (_, v), h in options.items() if h}, gp, ntl)
    exceptional_degrees = count = prime_count = 0
    for n, p, q in degrees:
        masks = set()
        for u, v in ((p, q), (q, p)):
            for h in options[u, v]:
                masks.update(exceptional_masks(n, u, v, h, factors[v]))
        for mask in sorted(masks):
            f = polynomial(mask)
            if f.factor()[1] != [(f, 1)] or X.pow_mod((2**p-1)*(2**q-1), f) != 1:
                raise ArithmeticError(f"invalid candidate in degree {n}")
            print(f"Degree {n}, exceptional mask {mask:#x}.")
        exceptional_degrees += bool(masks)
        count += len(masks)
        if not masks and pow(2, p, q) != 1:
            prime_count += 1
    print(f"Examined {len(degrees)} odd products of two distinct primes through {limit}. "
          f"{count} exceptional polynomials in {exceptional_degrees} degrees. "
          f"Full-degree prime powers forced in {len(degrees)-exceptional_degrees} degrees, "
          f"with primes forced in {prime_count} by the lifting criterion.")
    lifts = ((3, 7, 1, (7,)), (5, 31, 2, (31,)), (11, 23, 2, (23, 89)),
             (7, 127, 1, (127,)), (11, 89, 2, (23, 89)), (23, 47, 5, (47, 178481)))
    for p, q, tap, primes in lifts:
        n = p*q
        if n > limit:
            continue
        f = X**n+X**(q*tap)+1
        h = q*(2**p-1)
        if (prod(primes) != 2**p-1 or q not in primes or not all(fmpz(k).is_prime() for k in primes)
                or f.factor()[1] != [(f, 1)] or X.pow_mod(h, f) != 1
                or any(X.pow_mod(h//ell, f) == 1 or pow(2, p, ell) != 1 for ell in primes)):
            raise ArithmeticError(f"incorrect lifting exception in degree {n}")
        print(f"Degree {n}. The trinomial with tap {q*tap} has exact order {h}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=256, help="maximum semiprime degree")
    backend = parser.add_mutually_exclusive_group()
    backend.add_argument("--gp", metavar="EXECUTABLE", help="use PARI/GP to factor trinomials")
    backend.add_argument("--ntl", metavar="EXECUTABLE", help="use the compiled NTL factor enumerator")
    args = parser.parse_args()
    if args.through < 15:
        parser.error("expected a bound of at least 15")
    census(args.through, args.gp, args.ntl)
