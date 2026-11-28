"""Certify an ordinary count of primitive degree-1229 polynomials by a signed weight."""

from fractions import Fraction
from math import comb, floor, isqrt, prod

from check_primitive_weight_bound import krawtchouk_row


N = 1229
FIXED = 516
OBSERVED = 40
LEVEL = 160
TAIL_START = 85
CUTOFF = 305  # A positive score needs an odd weight strictly below this.
FREQUENCY = (101808133126899, 25258413561571, 6081049088867, 1416285931840,
             317871134706, 68414645634, 14029353531, 2716735113, 490355574,
             80796147, 11703889, 1371565, 100000)


def autocorrelation(d, frequency, weight):
    """Overlap between a radial frequency vector and its translate of given weight."""
    b = len(frequency) - 1
    return sum(comb(weight, a) * comb(d-weight, outside) *
               frequency[outside+a] * frequency[outside+weight-a]
               for a in range(weight+1)
               for outside in range(b-max(a, weight-a)+1))


def factor_capacities(max_degree):
    """Maximum number of distinct nonlinear irreducibles at a given total degree."""
    available = []
    counts = {1: 2}
    degree = 2
    while sum(available) < max_degree:
        counts[degree] = (2**degree - sum(k*v for k, v in counts.items() if degree % k == 0))//degree
        available.extend([degree]*counts[degree])
        degree += 1
    used = count = 0
    capacities = []
    for budget in range(max_degree+1):
        if count < len(available) and used + available[count] <= budget:
            used += available[count]
            count += 1
        capacities.append(count)
    return capacities


def tail_bound(d, observed, free, frequency, level, start):
    """Bound the signed tail by coding the additive characters of the divisor sieve."""
    mass = autocorrelation(d, frequency, 0)
    b = len(frequency)-1
    overlaps = [autocorrelation(d, frequency, w) for w in range(2*b+1)]
    tails = []
    for v in range(free+1):
        row = krawtchouk_row(free, v, free)
        tails.append(abs(sum((k-start)*row[k] for k in range(start+1, free+1))))
    density = Fraction(4, level+3)  # Upper bound on 1/G before the parity test.
    maximum_memory = 2*level+1
    capacity = factor_capacities(maximum_memory)
    local = [min(density, Fraction(5*level**3 * 3**capacity[f], 2**f))
             for f in range(maximum_memory+1)]
    weighted = density*tails[0]
    # Each character has a unique shortest recurrence. Its degree may include T+1.
    for lower in range(observed//2+1, maximum_memory+1, 4):
        upper = min(lower+3, maximum_memory)
        coefficient = max(local[lower-1:upper+1])
        blocks = d//(2*upper)
        extra = max(0, 2*upper-d-observed//2)
        overlap_sum = 0
        for w in range(d//upper, 2*b+1):
            words = comb(d, w) << extra
            if blocks:
                sparse = sum(comb(2*upper, k) for k in range(1, w//blocks+1))
                words = min(words, blocks*sparse)
            overlap_sum += words*overlaps[w]
        weighted += coefficient * Fraction(overlap_sum, mass) * max(tails[free//upper:])
    return weighted / (2 << free)


def signed_count():
    n, d, t = N, FIXED, OBSERVED
    group = 2**n - 1
    half = t//2
    free = n-1-2*d-t
    mass = autocorrelation(d, FREQUENCY, 0)
    peak = sum(comb(d, i)*g for i, g in enumerate(FREQUENCY))**2
    mean = Fraction(mass, 2**d)
    gain = Fraction(d * autocorrelation(d, FREQUENCY, 1), 2*mass)
    constant = CUTOFF - 2 - TAIL_START - Fraction(d+t, 2)
    if 99**2 < 2*70**2:
        raise ArithmeticError("invalid upper bound for the square root of two")
    sign_cost = sum((2*d+i) * 2**((i-1)//2) *
                    (Fraction(99, 70) if i % 2 == 0 else 1) for i in range(1, half+1))
    # Nineteen order primes and reciprocal sum <1/20000 suffice.
    small = (36871, 46703, 10543179280661916121033, 9536289355314392579996071515160583098298616686033085857)
    cofactor, remainder = divmod(group, prod(small))
    least = 818085338814611458
    if (remainder or cofactor >= least**16 or
            sum(Fraction(1, q) for q in small) + Fraction(15, least) >= Fraction(1, 20000)):
        raise ArithmeticError("the recorded order-prime budget does not apply")
    field_cost = 2*d*(abs(constant) + Fraction(d, 2) + 19*CUTOFF) + sign_cost
    field_sum = group*mean*(constant + gain - Fraction(CUTOFF, 20000))
    field_sum -= (isqrt(group)+1)*peak*field_cost
    tail = tail_bound(d, t, free, FREQUENCY, LEVEL, TAIL_START)
    score = field_sum - n*2**(n-1)*mean*tail
    count = floor(score / (n*CUTOFF*peak))
    if count <= 2**619 or 100*score <= 91*group*mean:
        raise ArithmeticError("the claimed count or normalized score failed")
    print(f"The normalized signed score exceeds {floor(1000*score/(group*mean))}/1000.")
    print(f"More than 2^{count.bit_length()-1} distinct primitive polynomials have at most "
          f"{CUTOFF-2} terms.")
    return count


if __name__ == "__main__":
    signed_count()
