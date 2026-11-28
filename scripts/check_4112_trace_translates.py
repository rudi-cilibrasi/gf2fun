"""Count primitive translates of y^j + y^(-j) and bound their binary weights."""

import argparse
import json
from math import gcd, prod

from check_4112_binomials import expand, orbits, read_rows
from check_4112_descent import DESCENT, M, TARGET, element, extension_rings, field_coordinate
from check_projective_4112 import A, B, K, ORDER, Q, ConstantField


def dickson_support():
    # D_n(V+1/V) = V^n + V^(-n) in characteristic two.
    previous, current = 0, 2
    for _ in range(1, M):
        previous, current = current, (current << 1) ^ previous
    return [i for i in range(M+1) if current >> i & 1]


def leading_weights(field, support):
    """Count the first 257 coefficients of each binary product, including its leading one."""
    constants, ring = extension_rings()
    values = [element(constants, c) for c in range(K)]
    zero, one = constants.zero(), constants.one()
    # Lucas' criterion gives [X^(M-t)] (X+p)^e in the relative factor.
    exponents = [[e-(M-t) for e in support if (M-t) & e == M-t] for t in range(M)]
    seen = set()
    minimum, count = M+1, 0
    for p in range(K):
        if p in seen or field.power(p, Q) == p:
            continue
        conjugates = {field.power(p, 2**i) for i in range(16)}
        if len(conjugates) != 16:
            raise ValueError("unexpected degree for a constant outside the subfield")
        seen.update(conjugates)
        count += 1
        leading = []
        for powers in exponents:
            coefficient = 0
            for e in powers:
                coefficient ^= field.power(p, e)
            leading.append(values[coefficient])
        product = ring(leading)
        for step in (1, 2, 4, 8):
            conjugate = ring([c.frobenius(step) for c in product.coeffs()])
            product = product.mul_low(conjugate, M)
        coeffs = product.coeffs()
        if any(v != zero and v != one for v in coeffs):
            raise ValueError("leading norm polynomial is not binary")
        minimum = min(minimum, sum(v == one for v in coeffs))
    if len(seen) != K-Q:
        raise ValueError("incomplete census of leading coefficients")
    return count, minimum


def trace_exponent(field, p, unit, logs, roots, conjugates, norms, radii, lines, base):
    """Compute L(v+1/v+p), using the monic quadratic T^2+pT+1."""
    if p == 0:
        return 2*logs[1] % B, "split"
    root = roots.get(field.divide(1, field.multiply(p, p)))
    if root is not None:
        r = field.multiply(p, root)
        return (logs[r] + logs[r ^ p]) % B, "split"

    s = field.multiply(p, conjugates[base])
    trace = s ^ conjugates[s]
    if trace == 0:
        points = lines[field.multiply(unit, p)]
        if len(points) != Q:
            raise ValueError("invalid affine line")
        return sum(logs[c] for c in points) % B, "line"

    b = field.multiply(base, field.divide(unit ^ conjugates[unit], trace))
    h = unit ^ norms[b] ^ field.multiply(p, conjugates[b])
    if h not in radii:
        raise ValueError("invalid circle radius")
    return sum(logs[b ^ c] for c in radii[h]) % B, "circle"


def count_orders(field, support, sample_powers):
    record = json.loads(DESCENT.read_text())
    cofactor = ORDER // prod(json.loads(TARGET.read_text())["known_prime_factors"])
    conjugates = [field.power(c, Q) for c in range(K)]
    norms = [field.power(c, M) for c in range(K)]
    roots = {field.multiply(c, c) ^ c: c for c in range(K)}
    radii = {field.exp[h*M]: [field.exp[h+(Q-1)*i] for i in range(M)]
             for h in range(Q-1)}
    dickson = []
    for p in range(K):
        value = 0
        for e in support:
            value ^= field.power(p, e)
        dickson.append(value)
    if sample_powers:
        f, x, y, embed = field_coordinate(record)

    full = primitive = 0
    for j, rows in read_rows().items():
        unit = field.power(record["unit"], j)
        logs = expand(rows, orbits(field, unit))
        base = field.exp[field.log[unit]//(Q-1)]
        if field.power(base, Q-1) != unit:
            raise ValueError("invalid circle parametrization")
        lines = {}
        for c in range(K):
            lines.setdefault(conjugates[c] ^ field.multiply(unit, c), []).append(c)
        sampled = set()
        if sample_powers:
            z = y.pow_mod(j, f) + y.pow_mod((-j) % (M*M), f)
        for p in range(K):
            e, method = trace_exponent(field, p, unit, logs, roots, conjugates, norms, radii, lines, base)
            if sample_powers and method not in sampled and p != conjugates[p]:
                if (z + embed(p)).pow_mod(A, f) != x.pow_mod(A*e, f):
                    raise ValueError(f"incorrect {method} exponent for j={j}, p={p}")
                sampled.add(method)
            if p == conjugates[p]:
                if e % cofactor:
                    raise ValueError("a subfield element has nonzero projected logarithm")
            else:
                if gcd(e, cofactor) != 1:
                    raise ValueError("a nonreal translate has deficient cofactor order")
                full += 1
            norm = dickson[p] ^ unit ^ conjugates[unit]
            if not norm:
                raise ValueError("zero relative norm")
            if gcd(field.log[norm], K-1) == 1 and gcd(e, B) == 1:
                primitive += 1
        if sample_powers and sampled != {"line", "circle", "split"}:
            raise ValueError("a direct power check is missing")
    return 16*primitive, 16*full


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sample-powers", action="store_true",
                        help="also directly power-check each type of identity in all sixteen charts")
    args = parser.parse_args()
    field = ConstantField()
    support = dickson_support()
    primitive, full = count_orders(field, support, args.sample_powers)
    reps, minimum = leading_weights(field, support)
    print(f"Among {(M-1)*K:,} distinct trace translates, {primitive:,} are primitive "
          f"and {full:,} have full projected cofactor order.")
    print(f"Across {reps:,} constant orbits the first {M} binary coefficients "
          f"of each full-degree polynomial contain at least {minimum} ones.")


if __name__ == "__main__":
    main()
