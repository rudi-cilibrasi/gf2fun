"""Prove five-row isolation for small Frobenius subgroups by exact specialization."""

from collections import Counter
from functools import cache
from itertools import combinations, permutations
from math import comb, gcd

from flint import fmpz, fmpz_poly

from check_factor_base import irreducible, modulus, polynomial
from check_kummer_sparse_orders import MULTIPLICITIES, cross, dot, row_charts


def cover(sizes, steps, weights, measure):
    """Cover all distinct projective residue points and return nonvanishing certificates.

    A positive measure is an absolute cyclotomic norm or a nonzero modular residue.
    Only the chosen pivots and final witnesses need to stay nonzero after specialization.
    """
    charts = [chart for t in steps for chart in row_charts(sizes, weights(t))]
    certificates = set()
    for normal in charts[0]:
        nonzero = [v for v in normal if measure(v)]
        if not nonzero:
            raise ArithmeticError("the first chart contains an identically zero collision form")
        certificates.add(min(measure(v) for v in nonzero))
        # A single nonzero coordinate forbids a residue of zero. Opposite
        # coordinates forbid equality of the corresponding two residues.
        if len(nonzero) == 1 or (len(nonzero) == 2 and not measure(sum(nonzero))):
            continue

        if len(normal) == 2:
            points = [(-normal[1], normal[0])]
        else:
            for other in charts:
                points = [cross(normal, second) for second in other]
                if all(any(measure(v) for v in point) for point in points):
                    break
            else:
                raise ArithmeticError(f"unresolved projective line for {sizes}")

        for point in points:
            certificates.add(min(measure(v) for v in point if measure(v)))
            if any(not measure(a-b) for a, b in combinations((0, *point), 2)):
                continue
            for chart in charts:
                values = []
                for form in chart:
                    value = measure(dot(form, point))
                    if not value:
                        break
                    values.append(value)
                else:
                    certificates.update(values)
                    break
            else:
                raise ArithmeticError(f"unresolved projective point for {sizes}: {point}")
    return certificates


def possible_specializations(p, norms):
    """Only q with ord_q(2) a power of p can be relevant to the descent."""
    primes = set()
    for norm in norms - {1}:
        power = 1
        while power*p < norm:
            power *= p
        # Every relevant q divides norm, hence its binary order is at most norm-1.
        divisor = gcd(norm, pow(2, power, norm) - 1)
        for prime, _ in fmpz(divisor).factor():
            q = int(prime)
            if not fmpz(q).is_prime() or q <= p or pow(2, power, q) != 1:
                raise ArithmeticError(f"unexpected specialization {p}, {q}")
            primes.add(q)
    return primes


def cyclotomic_primes(p):
    cyclotomic = fmpz_poly.cyclotomic(p)
    x = fmpz_poly([0, 1])
    powers = [x**i for i in range(p)]

    @cache
    def norm_of_coefficients(coefficients):
        return abs(int(cyclotomic.resultant(fmpz_poly(list(coefficients)))))

    def norm(value):
        reduced = fmpz_poly(value) % cyclotomic
        return norm_of_coefficients(tuple(map(int, reduced.coeffs())))

    norms = set()
    steps = range(1, p) if p <= 7 else (1,)
    for sizes in MULTIPLICITIES:
        norms.update(cover(sizes, steps, lambda t: [powers[t*i % p] for i in range(5)], norm))
    return possible_specializations(p, norms)


def check_specialization(p, q):
    generator = 2
    exponent = 1
    while pow(generator, p, q) != 1:
        generator = pow(generator, p, q)
        exponent += 1
    if generator == 1:
        raise ArithmeticError(f"missing subgroup of order {p} modulo {q}")
    for sizes in MULTIPLICITIES:
        cover(sizes, range(1, p), lambda t: [pow(generator, t*i, q) for i in range(5)],
              lambda value: value % q)
    return exponent


def check_modulo_31():
    # Every subset of at most four vertices of the 5-cycle is an arithmetic
    # progression for some nonzero step. Each block may use its own step.
    p, q = 5, 31
    weights = [pow(2, i, q) for i in range(p)]
    for size in range(1, 5):
        progressions = {frozenset((start + t*i) % p for i in range(size))
                        for start in range(p) for t in range(1, p)}
        if progressions != set(map(frozenset, combinations(range(p), size))):
            raise ArithmeticError("a within-block row set has no valid Frobenius step")
    failed = set()
    count = 0
    for sizes in MULTIPLICITIES:
        assignments = set(permutations(j for j, size in enumerate(sizes) for _ in range(size)))
        forms = [tuple(sum(w for w, j in zip(weights, way) if j == group)
                       for group in range(1, len(sizes))) for way in assignments]
        for residues in permutations(range(1, q), len(sizes) - 1):
            # Normalize a nonzero residue to 1. For the last layout the
            # other three labels are singletons and may be permuted freely.
            if residues[0] != 1:
                continue
            sums = Counter(dot(form, residues) % q for form in forms)
            if 1 in sums.values():
                continue
            if sizes != (2, 1, 1, 1):
                raise ArithmeticError(f"unresolved multiplicities {sizes} modulo 31")
            failed.add(min(tuple(sorted(x*pow(b, -1, q) % q for x in residues))
                           for b in residues))
    for taps in combinations(range(1, q), 3):
        orbit = min(tuple(sorted(x*pow(b, -1, q) % q for x in taps)) for b in taps)
        count += orbit in failed
    expected = {(1, 2, 8), (1, 3, 10), (1, 3, 22), (1, 5, 23),
                (1, 6, 11), (1, 6, 15), (1, 10, 22), (1, 12, 13)}
    if failed != expected or count != 240:
        raise ArithmeticError(f"unexpected projective exceptions {failed}, {count}")
    print("Modulo 31, only 240 distinct unordered residue triples in eight scalar orbits "
          "lack an isolated assignment.", flush=True)


def check_examples():
    x = polynomial(2)
    counts = Counter()
    group = 2**25 - 1
    for q in (601, 1801):
        if not fmpz(q).is_prime() or pow(2, 25, q) != 1 or pow(2, 5, q) == 1:
            raise ArithmeticError(f"expected binary order 25 at {q}")
    for interior in (1, 3):
        for taps in combinations(range(1, 25), interior):
            f = modulus(25, taps)
            if irreducible(f):
                for q in (601, 1801):
                    if x.pow_mod(group//q, f) == 1:
                        raise ArithmeticError(f"unexpected failed base test at {q}")
                    counts[q, interior] += 1
    for q, bits in ((601, 40), (1801, 44)):
        if (counts[q, 1], counts[q, 3]) != (4, 406) or (comb(25*q-1, 3)-1).bit_length() != bits:
            raise ArithmeticError(f"incorrect substitution counts for degree {25*q}")
    print("Both degrees 15025 and 45025 have four trinomial and 406 pentanomial "
          "exceptions outside the maximal-subfield product.", flush=True)

    # Rabin irreducibility and an independent full-degree-prime test.
    n, p, q, tap = 4805, 5, 31, 2667
    f = modulus(n, (1, 2, tap))
    if x.pow_mod(1 << n, f) != x or any(
        (x.pow_mod(1 << (n//d), f) - x).gcd(f) != 1 for d in (p, q)
    ):
        raise ArithmeticError("the degree-4805 example is reducible")
    group = 2**n - 1
    proper = (2**(n//p)-1) * (2**(n//q)-1)
    remaining = group
    while (shared := gcd(remaining, proper)) > 1:
        remaining //= shared
    if x.pow_mod(group//remaining, f) == 1:
        raise ArithmeticError("the example misses every full-degree prime")
    if 4 + 240*155**3 != 893730004 or (comb(n-1, 3)-1).bit_length() != 35:
        raise ArithmeticError("incorrect code budget for the degree-4805 tower")
    print("The degree-4805 example with taps 1, 2, 2667 has a full-degree order prime.", flush=True)


def main():
    higher = set()
    for p in (5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47):
        candidates = sorted(cyclotomic_primes(p))
        for q in candidates:
            if (p, q) != (5, 31):
                exponent = check_specialization(p, q)
                if exponent > 1:
                    higher.add((p, q, exponent))
        print(f"p={p}: {candidates}", flush=True)
    print(f"Specializations of binary order beyond p: {sorted(higher)}", flush=True)
    check_modulo_31()
    check_examples()


if __name__ == "__main__":
    main()
