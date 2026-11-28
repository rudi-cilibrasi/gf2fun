"""Recover the possible scalar orders from the fifteen pairings of an odd-degree support."""

import argparse
from itertools import combinations
from math import gcd

from check_scalar_pairs import scalar_residues


def excluded_triple(a, b, c, n, scalar_degree=None):
    step = gcd(b-a, c-a)
    m, width = (b-a)//step, (c-a)//step
    if width <= 6 or (width <= 22 and n % 3 != 0):
        return True

    for distance in (m, width-m):
        ratio, remainder = divmod(width, distance)
        if not remainder and ratio & (ratio-1) == 0 and gcd(ratio.bit_length()-1, n) == 1:
            return True

    # Unit differences give scalar degree i <= width and 5*n < 12*i*i*width.
    if any(gcd(delta, pow(2, n, delta)-1) != 1 for delta in (m, width-m, width)):
        return False
    if scalar_degree is not None:
        return scalar_degree > width or 5*n >= 12*scalar_degree**2*width
    if width <= 1000:
        # The exact subgroup census leaves only these odd scalar degrees.
        largest = max((i for i in (3, 5, 9) if i <= width and n % i == 0), default=0)
    else:
        largest = width
    return 5*n >= 12*largest**2*width


def gap_candidates(support, scalar_degree=None):
    n = support[-1]
    if len(support) != 5 or support != sorted(set(support)) or support[0] != 0 or n % 2 != 1:
        raise ValueError("expected five distinct increasing exponents starting at zero and ending at an odd degree")
    if gcd(*support) != 1:
        raise ValueError("first divide all exponents by their common gcd")
    if scalar_degree is not None and (scalar_degree < 2 or n % scalar_degree
            or n//scalar_degree <= scalar_degree or gcd(n//scalar_degree,scalar_degree) != 1):
        raise ValueError("the smaller scalar degree must give a proper coprime partition")
    if any(excluded_triple(a, b, c, n, scalar_degree) for a, b, c in combinations(support, 3)):
        return
    for c in support:
        a,*rest = [e for e in support if e != c]
        for b in rest:
            d,e = [value for value in rest if value != b]
            first, second = b-a,e-d
            if first == second:
                continue
            gap = gcd(first,second)
            # The quotient by the scalar order is 1, 2 or 3, and the order is coprime to 6.
            multiplier = gcd(gap,6)
            h = gap//multiplier
            if multiplier > 3 or h <= 1 or gcd(h,6) != 1 or len({a%h,d%h,c%h}) != 3:
                continue
            if pow(2,scalar_degree or n,h) != 1:
                continue
            if scalar_degree is not None and not (3*scalar_degree**2 <= 4*h
                    and 5*gap < 12*scalar_degree**2 and 3*h <= n):
                continue
            small,large = sorted((first,second))
            ratio,rem = divmod(large,small)
            if rem == 0 and ratio & (ratio-1) == 0:
                start,other = (a,d) if first == small else (d,a)
                distance = abs(other+(ratio-1)*c-ratio*start)
                if distance == 0:  # The scalar field has odd degree.
                    continue
                if scalar_degree is not None:
                    partner = n//scalar_degree
                    order_multiple = gcd(distance,pow(2,partner,distance)-1)
                    if 4*order_multiple < 3*partner**2:
                        continue
            yield c,(a,b),(d,e),gap,h


def count_gap_survivors(n,p):
    """Count the prime-degree paired supports passing the new gap bound, before polynomial gcds."""
    h = (1 << p)-1
    choices = n//h
    limit = (12*p*p-1)//(5*h)
    allowed = sum(gcd(a,b) <= limit for a in range(1,choices+1) for b in range(1,choices+1))
    residues = scalar_residues(n,p,{3:0b1011,5:0b100101}[p])
    classes = {}
    for v in residues:
        size = (n-v)//h+1
        classes[size] = classes.get(size,0)+1
    total = 0
    for size,nclasses in classes.items():
        free = sum((size-b)*sum(gcd(a,b) <= limit for a in range(1,choices+1))
                   for b in range(1,size))
        total += nclasses*(size*allowed+2*free)
    return total


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("exponents",type=int,nargs=5)
    parser.add_argument("--scalar-degree",type=int)
    args = parser.parse_args()
    candidates = list(gap_candidates(args.exponents,args.scalar_degree))
    for c,a,b,g,h in candidates:
        print(f"singleton {c}, pairs {a}, {b}, gap gcd {g}, candidate scalar order {h}")
    print(f"{len(candidates)} of 15 pairings survive the integer tests.")
