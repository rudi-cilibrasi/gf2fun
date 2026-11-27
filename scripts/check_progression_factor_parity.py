"""Check the progression parity formula over four fields and the binary examples in the note."""

import json
from math import prod

from flint import fmpz, fq_default_poly_ctx, nmod_poly

from check_factor_base import DATA
from check_product_range import prime_index_powers


def parity_checks():
    checked = 0
    for extension in (1, 2, 3, 4):
        ring = fq_default_poly_ctx(2, extension, 'w')
        field = ring.base_field()
        w = field.gen()
        if w.is_zero():
            w = field.one()
        x = ring.gen()
        for b in (4, 8, 12):
            for d in (x + ring([w]), x**2 + ring([w])*x + ring([w**2])):
                base = (1 + x**b) * d.compose(x**(2*b))
                for a in (1, b+1, base.degree()-1):
                    f = base + ring([w])*x**a
                    unit, factors = f.factor()
                    if (unit != 1 or any(k != 1 for _, k in factors)
                            or prod((p for p, _ in factors), start=ring.one()) != f):
                        raise ArithmeticError(f'incorrect squarefree factorization at {(extension, b, a)}')
                    if len(factors) % 2 != (extension % 2 == 1 and b % 8 == 4):
                        raise ArithmeticError(f'factor parity disagreement at {(extension, b, a)}')
                    checked += 1
    print(f'Checked {checked} squarefree factorizations over GF(2), GF(4), GF(8) and GF(16).')


def progression_witness(n, b, a, factor_table):
    x = nmod_poly([0, 1], 2)
    f = (1 + x**b) * (1 + x**(n-b)) + x**a
    order = 2**n - 1
    with (DATA / factor_table).open() as source:
        factors = json.load(source)[str(n)]
    primes = sorted(set(factors))
    if prod(factors) != order or not all(fmpz(p).is_prime() for p in primes):
        raise ArithmeticError(f'invalid factorization of the degree-{n} group order')
    if x.pow_mod(order, f) != 1 or any(v == 1 for _, v in prime_index_powers(x, order, primes, f)):
        raise ArithmeticError(f'the degree-{n} progression witness failed an order test')
    print(f'Degree {n} with a={a}, b={b}: full order from {len(primes)} prime-index tests.')


def degree_twelve():
    x = nmod_poly([0, 1], 2)
    base = (1 + x**4) * (1 + x**8)
    for a, degrees in ((1, [3, 4, 5]), (3, [2, 4, 6]), (5, [12])):
        f = base + x**a
        if sorted(p.degree() for p, e in f.factor()[1] for _ in range(e)) != degrees:
            raise ArithmeticError(f'unexpected factor degrees at tap {a}')
    witness = base + x**5
    if x.pow_mod(273, witness) != 1 or any(x.pow_mod(273//p, witness) == 1 for p in (3, 7, 13)):
        raise ArithmeticError('incorrect order of the irreducible degree-12 pair')
    print('Degree 12: the single irreducible reciprocal pair in the family has root order 273.')


def quaternary_factor():
    n = 7560
    x = nmod_poly([0, 1], 2)
    f = x**n + x**121 + x**107 + x**14 + 1
    cube_root = x.pow_mod((2**n - 1)//3, f)
    quaternary = fq_default_poly_ctx(2, 2, 'w')
    omega = quaternary.base_field().gen()
    lifted = quaternary(list(map(int, f)))
    factor = lifted.gcd(quaternary(list(map(int, cube_root))) + quaternary([omega]))
    conjugate = quaternary([coefficient**2 for coefficient in factor])
    weight = sum(not coefficient.is_zero() for coefficient in factor)
    if (factor * conjugate != lifted or factor == conjugate
            or factor.degree() != n//2 or weight != 2831):
        raise ArithmeticError('the degree-7560 quaternary factor disagrees')
    print(f'Degree {n}: each degree-{n//2} quaternary factor has {weight} terms.')


if __name__ == '__main__':
    parity_checks()
    degree_twelve()
    progression_witness(5964, 28, 1573, 'mersenne-4097-5964.json')
    progression_witness(6300, 84, 13, 'mersenne-4224-7560-extra.json')
    quaternary_factor()
