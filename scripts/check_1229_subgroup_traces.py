"""Exclude a thin coefficient prefix among all degree-1229 factors of X^(36871*46703)+1."""

import csv

from check_degree_1229 import GROUP, N, PRIMES
from check_factor_base import DATA, irreducible, modulus, polynomial
from period_coordinate import mask_of


def multiplication_table(multiplier, field):
    """Precompute multiplication by one field element on eight coefficient bits at a time."""
    n = field.bit_length()-1
    table = []
    for _ in range((n+7)//8):
        row = [0]
        for _ in range(8):
            row += [a ^ multiplier for a in row]
            multiplier <<= 1
            if multiplier >> n:
                multiplier ^= field
        table.append(row)
    return table


def multiply(value, table):
    result = 0
    for row, digit in zip(table, value.to_bytes(len(table), 'little')):
        result ^= row[digit]
    return result


def minimal_polynomial(root, field):
    """Recover the first binary dependence among 1, root, ..., root^n."""
    table = multiplication_table(root, field)
    basis = {}
    value = 1
    for i in range(N+1):
        column, relation = value, 1 << i
        while column:
            lead = column.bit_length()-1
            if lead not in basis:
                basis[lead] = (column, relation)
                break
            v, r = basis[lead]
            column ^= v
            relation ^= r
        if not column:
            return relation
        value = multiply(value, table)
    raise ArithmeticError("missing minimal polynomial")


def powers(generator, order, field):
    table = multiplication_table(generator, field)
    result = []
    y = 1
    for _ in range(order):
        result.append(y)
        y = multiply(y, table)
    if y != 1 or len(set(result)) != order:
        raise ArithmeticError("incorrect field multiplication table or subgroup generator")
    return result


def frobenius_orbits(prime, degree):
    """Index exponents by their representative and the number of squarings from it."""
    orbit, shift = [0]*prime, [0]*prime
    reps = [0]
    for a in range(1, prime):
        if orbit[a]:
            continue
        index = len(reps)
        reps.append(a)
        b = a
        for k in range(degree):
            if orbit[b]:
                raise ArithmeticError("short or overlapping Frobenius orbit")
            orbit[b], shift[b] = index, k
            b = 2*b % prime
        if b != a:
            raise ArithmeticError("the orbit does not close")
    return reps, orbit, shift


def power_traces(field):
    """Trace of 1, X, ..., X^(2n-2) by Newton sums for the field modulus."""
    n = field.bit_length()-1
    indices = [i for i in range(1, n+1) if field >> (n-i) & 1]
    traces = [n % 2]
    for k in range(1, 2*n-1):
        rhs = (k % 2) * (k in indices)
        traces.append((rhs + sum(traces[k-i] for i in indices if i < k)) % 2)
    return sum(bit << i for i, bit in enumerate(traces))


def check(limit=127):
    if not 1 <= limit < N//2:
        raise ValueError("expected disjoint endpoint windows")
    p, q = PRIMES[:2]
    f = modulus(N, (2, 6, 15))
    x = polynomial(2)
    if not irreducible(f):
        raise ArithmeticError("reducible field modulus")
    alpha = x.pow_mod(GROUP//p, f)
    beta = x.pow_mod(GROUP//q, f)
    if alpha == 1 or alpha.pow_mod(p, f) != 1 or beta == 1 or beta.pow_mod(q, f) != 1:
        raise ArithmeticError("incorrect prime-order projections")
    field = mask_of(f)
    with (DATA / "degree-1229-small-subgroup-weights.csv").open(newline="") as source:
        extrema = list(csv.DictReader(source))
    if [int(row["order"]) for row in extrema] != [p, q, p*q]:
        raise ValueError("incomplete subgroup table")
    for row in extrema:
        a, b = int(row["alpha_exponent"]), int(row["beta_exponent"])
        root = alpha.pow_mod(a, f)*beta.pow_mod(b, f) % f
        poly = minimal_polynomial(mask_of(root), field)
        if poly.bit_length() != N+1 or poly.bit_count() != int(row["min_weight"]):
            raise ArithmeticError("the listed minimum-weight witness failed")
    beta_powers = powers(mask_of(beta), q, field)
    reps, orbit, shift = frobenius_orbits(p, N)
    other_reps, _, _ = frobenius_orbits(q, N)
    trace = power_traces(field)
    rows = []
    for a in reps:
        y = mask_of(alpha.pow_mod(a, f))
        functional = sum(((y & (trace >> i)).bit_count() % 2) << i for i in range(N))
        rows.append(bytes((functional & z).bit_count() % 2 for z in beta_powers))

    tested = 0
    last = 0
    for a in reps:
        exponents = range(q) if a else other_reps[1:]
        survivors = [(b, 0) for b in exponents]
        tested += len(survivors)
        for k in range(1, limit+1, 2):
            e = a*k % p
            row = rows[orbit[e]]
            multiplier = k*pow(2, -shift[e], q) % q
            remaining = []
            for b, first in survivors:
                bit = row[b*multiplier % q]
                if first == 0:
                    remaining.append((b, k if bit else 0))
                elif bit == (k % first == 0):
                    remaining.append((b, first))
            survivors = remaining
            if not survivors:
                last = max(last, k)
                break
        if survivors:
            raise ArithmeticError(f"{len(survivors)} one-tap prefixes survive for exponent {a}")
    if tested*N != p*q-1:
        raise ArithmeticError("incomplete subgroup coverage")
    print(f"All {tested:,} nonidentity conjugacy classes need at least two interior coefficients "
          f"within {last} positions of each endpoint.")


if __name__ == "__main__":
    check()
