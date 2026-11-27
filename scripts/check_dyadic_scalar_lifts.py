"""Multiply the scalar-conjugate trinomial factors of the dyadic five-term lifts."""

from math import gcd


def product(a, b, modulus):
    value = 0
    while b:
        if b & 1:
            value ^= a
        b >>= 1
        a <<= 1
        if a.bit_length() == modulus.bit_length():
            a ^= modulus
    return value


def check_lift(source, singleton, k, expected):
    j = source[-1]
    if k not in (2,4) or gcd(k,j) != 1:
        raise ValueError("the scalar and trinomial degrees must be coprime")
    m = (1 << k)-1
    modulus = (1 << k) | 3
    powers = [1]
    for _ in range(1,m):
        powers.append(product(powers[-1],2,modulus))
    if len(set(powers)) != m or product(powers[-1],2,modulus) != 1:
        raise ValueError("the scalar polynomial is not primitive")
    e,f = [i-singleton for i in source if i != singleton]
    if (e-f) % m:
        raise ValueError("the two residues must agree")
    scalar_log = pow(e,-1,m)
    exponents = [0,e,f,k*e,k*f]
    support = tuple(sorted(t-min(exponents) for t in exponents))
    if support != expected or len(set(support)) != 5 or support[-1] != k*j:
        raise ValueError("incorrect normalized five-term support")

    # For alpha^e a root of T^k+T+1, the monic factor at alpha is
    # alpha^j g(X/alpha). Multiply all k binary Frobenius conjugates.
    result = {0:1}
    for t in range(k):
        next_product = {}
        for i in source:
            coeff = powers[((1 << t)*scalar_log*(j-i)) % m]
            for old,c in result.items():
                next_product[old+i] = next_product.get(old+i,0) ^ product(coeff,c,modulus)
        result = {i:c for i,c in next_product.items() if c}
    if result != dict.fromkeys(support,1):
        raise ArithmeticError("the scalar-conjugate factorization disagrees")
    print(f"Degree {k*j}, support {support}, order {m}*(2^{j}-1), norm has degree {j}.")


if __name__ == "__main__":
    # Each source is primitive by the small-degree, Ore, or degree-22327 certificate.
    check_lift((0,1,3),1,2,(0,1,2,4,6))
    check_lift((0,3,2047),2047,2,(0,6,2047,2050,4094))
    check_lift((0,511,2047),0,2,(0,511,1022,2047,4094))
    check_lift((0,2445,22327),22327,4,(0,9780,66981,69426,89308))
