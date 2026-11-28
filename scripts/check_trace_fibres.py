"""Recover every possible monic polynomial with the initial traces of a known irreducible."""

from check_degree_1229 import GROUP, N, PRIMES
from check_factor_base import irreducible, modulus, polynomial


def possible_polynomials(f, finite, infinity):
    """Enumerate the affine space before testing its elements for irreducibility and poles."""
    n = f.degree()
    if (n < 2 or not irreducible(f) or finite.is_zero() or
            infinity < 0 or f.gcd(finite) != 1):
        raise ValueError("expected an irreducible template and a divisor away from its roots")
    common, inverse, _ = f.derivative().xgcd(f)
    if common != 1:
        raise ArithmeticError("the template is inseparable")
    scale = finite.pow_mod(2, f)*inverse % f
    free_bits = max(0, n - finite.degree() - infinity)
    for mask in range(1 << free_bits):
        t = polynomial(mask)
        yield f + (scale*t*t % f)


def same_record(f, h, finite, infinity):
    """Compare the logarithmic derivatives at finite points and on the reciprocal chart."""
    if h.gcd(finite) != 1:
        return False
    if (f.derivative()*h + h.derivative()*f) % (finite*finite) != 0:
        return False
    a, b = f.reverse(), h.reverse()
    return (a.derivative()*b + b.derivative()*a) % polynomial(1 << (2*infinity)) == 0


def check_small():
    x = polynomial(2)
    for n in (5, 6, 7):
        irreds = [polynomial(mask) for mask in range(2**n+1, 2**(n+1), 2)
                  if irreducible(polynomial(mask))]
        for f in irreds:
            for d, e in ((x*x*(x+1), 1), (x*x+x+1, n-3), (x, n-1), (x+1, n+1)):
                expected = [h for h in irreds if same_record(f, h, d, e)]
                candidates = list(possible_polynomials(f, d, e))
                decoded = [h for h in candidates if irreducible(h) and h.gcd(d) == 1]
                if len(decoded) != len(expected) or any(h not in expected for h in decoded):
                    raise ArithmeticError(f"trace decoding disagrees with exhaustion in degree {n}")


def check_pair(first, second, finite, infinity, failed):
    f, h = modulus(N, first), modulus(N, second)
    if (finite.degree()+infinity != N-1 or list(possible_polynomials(f, finite, infinity)) != [f, h]
            or not irreducible(h) or not same_record(f, h, finite, infinity)):
        raise ArithmeticError("incorrect list for the trace record")
    x = polynomial(2)
    for poly, expected in zip((f, h), failed):
        if [p for p in PRIMES if x.pow_mod(GROUP//p, poly) == 1] != expected:
            raise ArithmeticError("incorrect prime-index failures")
    print(f"Exactly {first} and {second} match the {N-1}-bit record. Prime-test failures {failed}.")


def check_shorter(first, second, finite, infinity):
    f, h = modulus(N, first), modulus(N, second)
    x = polynomial(2)
    small = polynomial(1)
    for d in range(1, 9):
        small *= x**(2**d) + x
    matches = []
    for candidate in possible_polynomials(f, finite, infinity):
        # For prime N, the irreducible factors of X^(2^N)-X have degree 1 or N.
        if candidate.gcd(small) == 1 and x.pow_mod(1 << N, candidate) == x:
            matches.append(candidate)
    if len(matches) != 2 or f not in matches or h not in matches:
        raise ArithmeticError("unexpected irreducible in the enlarged affine space")
    bits = finite.degree() + infinity
    print(f"{bits} bits, {2**(N-bits)} monic candidates, exactly the two stated irreducibles.")


if __name__ == "__main__":
    check_small()
    x = polynomial(2)
    residual = x**17+x**13+x+1
    factors = sorted((f.degree(), e) for f, e in residual.factor()[1])
    if factors != [(1, 1), (3, 1), (13, 1)]:
        raise ArithmeticError("incorrect finite trace locations")
    check_pair([162, 170, 604], [136, 138, 604], x**682*residual, 529, ([36871], []))
    check_shorter([162, 170, 604], [136, 138, 604], x**682*residual, 522)
    residual = (1+x**17+x**18+x**76)*(1+x**217+x**221+x**302)+x**302
    check_pair([34, 36, 152], [625, 1059, 1067], x**312*residual, 538, ([46703], [36871]))
    check_shorter([34, 36, 152], [625, 1059, 1067], x**311*residual, 530)
