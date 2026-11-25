"""Enumerate low-degree irreducible factors of Dickson substitutions using roots of unity."""

from collections import defaultdict
from functools import lru_cache

from check_factor_base import polynomial
from make_witnesses import mask_product, prime_factors, remainder
from period_coordinate import dickson_value, mask_of


@lru_cache(maxsize=32768)
def at_root(m, mask):
    f = polynomial(mask)
    return mask_of(dickson_value(m, polynomial(2) % f, f))


def torus_order(mask):
    """Order of y for a root y+y^-1 of the binary irreducible with this mask."""
    d = mask.bit_length()-1
    order = (1 << d)-1
    if at_root(order, mask) != 0:
        order += 2
    if at_root(order, mask) != 0:
        raise ArithmeticError("the quadratic roots are in neither possible torus")
    for prime in sorted(set(prime_factors(order))):
        while order % prime == 0 and at_root(order//prime, mask) == 0:
            order //= prime
    return order


def minimal_polynomial(value, modulus):
    """Find the first binary linear dependence among 1, value, value², ... ."""
    basis = {}
    power = 1
    for j in range(modulus.bit_length()):
        coefficients = 1 << j
        v = power
        while v.bit_length() in basis:
            entry, relation = basis[v.bit_length()]
            v ^= entry
            coefficients ^= relation
        if v == 0:
            return coefficients
        basis[v.bit_length()] = v, coefficients
        power = remainder(mask_product(power, value), modulus)
    raise ArithmeticError("the powers exceeded the dimension without a dependence")


def prime_fibres(masks):
    """Yield (m,P,factors) for all completely smooth P(D_m) with m an odd prime."""
    groups = defaultdict(list)
    for mask in masks:
        groups[torus_order(mask)].append(mask)
    for s, preimages in sorted(groups.items()):
        for m in sorted(set(prime_factors(s))):
            t = s//m
            if t not in groups:
                continue
            fibres = defaultdict(dict)
            for q in preimages:
                p = minimal_polynomial(at_root(m, q), q)
                fibres[p][q] = 2 if t == 1 else 1
            if t % m:
                for q in groups[t]:
                    p = minimal_polynomial(at_root(m, q), q)
                    fibres[p][q] = 1
            for p, factors in sorted(fibres.items()):
                if p not in groups[t] or sum((q.bit_length()-1)*e for q, e in factors.items()) != m*(p.bit_length()-1):
                    raise ArithmeticError("incomplete Dickson fibre")
                yield m, p, sorted(factors.items())
