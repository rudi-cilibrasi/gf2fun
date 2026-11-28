"""Count distinguishable quotients of elliptic functions in two pentanomial degrees."""

from collections import Counter
from itertools import product
from math import comb, gcd, isqrt

from flint import arb, fmpz, nmod_poly

from check_elliptic_pentanomial_order import check_integer_order, coprime_pairs


# Diameter and largest a in each nested set of Eisenstein lattice pairs.
STAGES = (
    (1, 2305610), (2, 2177145), (3, 1783278), (4, 1693068),
    (6, 1453721), (8, 1270122), (12, 1093353), (16, 937354),
    (24, 796289), (32, 676354), (48, 570996), (64, 482893),
    (96, 406484), (128, 343060), (192, 288375), (256, 243139),
    (384, 204244), (512, 172122),
)
NUMERATOR = (1, 16, 36, 16, 1)


def local_choices(diameter):
    """Count five integer coordinates of fixed sum and bounded negative part."""
    radius, offset = divmod(diameter, 2)
    return sum(
        (-1)**j * comb(4, j) * comb(radius-j+4+offset, 4) * comb(radius-j+4, 4)
        for j in range(min(radius, 4) + 1)
    )


def check_large_degree():
    degree = 2**84 + 2
    index = check_integer_order(degree)
    counts = [coprime_pairs(limit) for _, limit in STAGES] + [(0, 0)]
    cost = scaled_bits = 0
    scale = 2048
    for i, (diameter, _) in enumerate(STAGES):
        count = counts[i][0] - counts[i+1][0]
        norm_sum = counts[i][1] - counts[i+1][1]
        cost += diameter * norm_sum
        scaled_bits += count * ((local_choices(diameter)**scale).bit_length() - 1)
    bits = scaled_bits // scale - (index - 1).bit_length()
    if 2*cost >= degree or index != 3 or bits != 10134308948149:
        raise ArithmeticError("incorrect elliptic function diameter or count")
    print(f"degree {degree}, total diameter {cost}, root order at least 2^{bits}")


def norm_counts(limit):
    counts = Counter()
    for a in range(2, isqrt(4*limit//3) + 1):
        for b in range(1, a):
            norm = a*a - a*b + b*b
            if norm <= limit and (a+b) % 3 and gcd(a, b) == 1:
                counts[norm] += 1
    return counts


def height_count_mod(limit, counts, prime):
    """Sum coefficients through limit in the product of the local height series."""
    # The jth coefficient of q*(log L)' is 4 minus the jth power sum
    # for the four inverse roots of the local numerator.
    factors = [0] * (limit // min(counts) + 1)
    powers = [0]
    for j in range(1, len(factors)):
        total = j * NUMERATOR[j] if j < len(NUMERATOR) else 0
        total += sum(NUMERATOR[i]*powers[j-i] for i in range(1, min(4, j-1)+1))
        powers.append(-total % prime)
        factors[j] = 4 - powers[j]
    logarithmic_derivative = [0] * limit
    for norm, multiplicity in counts.items():
        weight = norm * multiplicity
        for j in range(1, limit//norm + 1):
            logarithmic_derivative[j*norm - 1] += weight * factors[j]
    logarithm = nmod_poly([a % prime for a in logarithmic_derivative], prime).integral()
    series = nmod_poly([1], prime)
    precision = 1
    while precision <= limit:
        precision = min(2*precision, limit + 1)
        derivative = series.derivative().mul_low(series.inverse_series_trunc(precision-1), precision-1)
        correction = 1 + logarithm.truncate(precision) - derivative.integral()
        series = series.mul_low(correction, precision)
    return sum(int(c) for c in series) % prime


def height_count_upper_bound(limit, counts):
    """Bound the partial coefficient sum by the generating function at 132/133."""
    q = arb(132) / 133
    logarithm = -limit * q.log()
    for norm, multiplicity in counts.items():
        y = q**norm
        numerator = ((y + 16)*y + 36)*y*y + 16*y + 1
        logarithm += multiplicity * (numerator.log() - 4*(1-y).log())
    return logarithm / arb(2).log()


def check_small_degree():
    degree = 2**18 + 2
    factors = (2, 3, 43691)
    if (2*3*43691 != degree or not all(fmpz(p).is_prime() for p in factors)
            or pow(2, degree, degree+1) != 1
            or any(pow(2, degree//p, degree+1) == 1 for p in factors)):
        raise ArithmeticError("failed integer primitive-root certificate")
    index = gcd(degree, pow(2, degree, degree)-1)
    if index != 3:
        raise ArithmeticError("incorrect group index allowance")
    limit = (degree-1)//4
    counts = norm_counts(limit)
    combined, modulus = 0, 1
    prime = 2**30
    while modulus.bit_length() < 1500:
        prime += 1
        while not fmpz(prime).is_prime():
            prime += 1
        value = height_count_mod(limit, counts, prime)
        step = (value-combined) * pow(modulus, -1, prime) % prime
        combined += modulus*step
        modulus *= prime
    if not height_count_upper_bound(limit, counts) < 1396 or modulus < 2**1396:
        raise ArithmeticError("CRT modulus does not certify the exact count")
    bits = (combined//index).bit_length() - 1
    if bits != 1387 or combined <= 3 * 2**1387:
        raise ArithmeticError("incorrect degree-262146 count")
    print(f"degree {degree}, height budget {limit}, root order at least 2^{bits}")


def check_height_series():
    for diameter in range(7):
        radius, offset = divmod(diameter, 2)
        count = 0
        for first in product(range(-radius, radius+offset+1), repeat=4):
            vector = (*first, offset-sum(first))
            count += sum(-x for x in vector if x < 0) <= radius
        if count != local_choices(diameter):
            raise ArithmeticError("incorrect local lattice point count")
    # Compare the logarithmic-derivative calculation to an exact direct product.
    limit = 120
    counts = norm_counts(limit)
    coefficients = [1] + [0]*limit
    for norm, multiplicity in counts.items():
        for _ in range(multiplicity):
            updated = coefficients.copy()
            for j in range(1, limit//norm + 1):
                choices = local_choices(2*j) - local_choices(2*j-2)
                for i in range(limit+1-j*norm):
                    updated[i+j*norm] += choices*coefficients[i]
            coefficients = updated
    for prime in (127, 65537):
        if sum(coefficients) % prime != height_count_mod(limit, counts, prime):
            raise ArithmeticError("height series disagrees with direct enumeration")


def check_prime_components():
    x = nmod_poly([0, 1], 2)
    checked_primes = set()
    for dilation in range(3, 26, 2):
        for m in range(2, 110//dilation + 1):
            degree = dilation*m
            modulus = x**degree + x**dilation + 1
            if modulus.factor()[1] != [(modulus, 1)]:
                continue
            for p, exponent in fmpz(dilation).factor():
                p = int(p)
                e = next(j for j in range(1, p) if pow(2, j, p) == 1)
                predicted = p**exponent
                base_order = 2**e - 1
                while base_order % p == 0:
                    predicted *= p
                    base_order //= p
                cofactor = 2**degree - 1
                while cofactor % p == 0:
                    cofactor //= p
                value = (1+x).pow_mod(cofactor, modulus)
                if value.pow_mod(predicted, modulus) != 1 or value.pow_mod(predicted//p, modulus) == 1:
                    raise ArithmeticError(f"incorrect {p}-part in degree {degree}")
                checked_primes.add(p)
    if not {3, 5, 7} <= checked_primes:
        raise ArithmeticError("missing test for a prime component")


if __name__ == "__main__":
    check_height_series()
    check_prime_components()
    check_large_degree()
    check_small_degree()
