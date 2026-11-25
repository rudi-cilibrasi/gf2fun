"""Classify product-one triples of X^(2^s+d) + X^5 + X^3 + X^2 + 1 at fixed d."""

import argparse
from math import lcm

from sympy import Poly, divisors, resultant, symbols

from check_dyadic_triples import EMPTY, ONE, T, Quadratic, image_symmetric, normalize
from check_exterior import fixed_dimension
from make_witnesses import gcd, mask_product, remainder, x_power


def exceptional_parameters(offset):
    """Every possible t=u+v is a root of the returned binary polynomial."""
    zero, one = Quadratic(EMPTY, EMPTY), Quadratic(ONE, EMPTY)
    u, v = Quadratic(EMPTY, T), Quadratic(T, T)
    norms = []
    for _ in range(2):
        u, v, _ = image_symmetric(u, v, zero, one, offset)
        total = u + v
        defect = total*total*total * (total*total + u*v) + one
        norm = defect.norm()
        norms.append(normalize(norm)[1] if norm else 0)
    common = gcd(*norms)
    if not common:
        raise ValueError(f"both parameter norms vanish identically at offset {offset}")
    return common


def polynomial_mask(poly):
    return sum(1 << i for (i,), coefficient in poly.terms() if int(coefficient) % 2)


def root_factors(parameter_mask):
    """Eliminate b, then t, from the cubic for a hypothetical triple."""
    x, t = symbols("x t")
    parameters = Poly.from_dict({(i,): 1 for i in range(parameter_mask.bit_length())
                                 if parameter_mask >> i & 1}, t, modulus=2)
    # The cubic is a + t*w*b. Its norm in b times t³ has no negative powers.
    a = x**3 + t*x + 1
    w = x**2 + x
    norm = t**3 * (a**2 + t*w*a + t**2*w**2) + w**2
    factors = set()
    for irreducible, _ in parameters.factor_list()[1]:
        eliminated = Poly(resultant(irreducible.as_expr(), norm, t), x, modulus=2)
        for factor, _ in eliminated.factor_list()[1]:
            factors.add(polynomial_mask(factor))
    return sorted(factors)


def first_three_pass(offset, s, factors):
    common = 1
    for factor in factors:
        degree = factor.bit_length() - 1
        exponent = ((1 << (s % degree)) + offset) % ((1 << degree) - 1)
        if x_power(exponent, factor) == remainder(0x2d, factor):
            common = mask_product(common, factor)
    degree = common.bit_length() - 1
    taps = [i for i in range(degree) if common >> i & 1]
    return all(fixed_dimension(degree, taps, k) == 0 for k in range(1, min(degree, 3) + 1))


def classify(offset):
    parameters = exceptional_parameters(offset)
    factors = root_factors(parameters)
    period = lcm(*(factor.bit_length() - 1 for factor in factors))
    passes = [first_three_pass(offset, s, factors) for s in range(period)]
    period = next(int(d) for d in divisors(period)
                  if all(value == passes[s % d] for s, value in enumerate(passes)))
    return parameters, passes[:period]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("offset", type=int, nargs="*", default=list(range(-3, 10)))
    for d in parser.parse_args().offset:
        parameters, passes = classify(d)
        period = len(passes)
        print(f"d={d:3}, parameter gcd={parameters:#x}, period={period}, "
              f"passing residues={[i for i, value in enumerate(passes) if value]}")
        if -3 <= d <= 9 and d not in (2, 5):
            for s in range(lcm(3, period)):
                if passes[s % period] != ((pow(2, s, 7) + d) % 7 not in (0, 5)):
                    raise ArithmeticError(f"degree-seven congruence disagreement for d={d}, s={s}")
        for s in range(6):
            n = (1 << s) + d
            if 5 < n <= 40:
                direct = all(fixed_dimension(n, [0, 2, 3, 5], k) == 0 for k in (1, 2, 3))
                if direct != passes[s % period]:
                    raise ArithmeticError(f"direct exterior-power disagreement for d={d}, s={s}")
