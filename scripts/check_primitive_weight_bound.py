"""Check the asymptotic weight and entropy bounds and the exact counts for degree 1229."""

from fractions import Fraction
from math import ceil, comb, factorial, isqrt, prod


def reduced_log_bounds(x):
    """Enclose the natural logarithm of a rational in [1,2] by its atanh series."""
    assert 1 <= x <= 2
    t = (x-1)/(x+1)
    partial = 2*sum(t**(2*j+1)/(2*j+1) for j in range(12))
    return partial, partial + 2*t**25/(25*(1-t*t))


def entropy_bounds(p):
    ln2_lo, ln2_hi = reduced_log_bounds(Fraction(2))
    lower = upper = Fraction(0)
    for mass in (p, 1-p):
        x, k = 1/mass, 0
        while x >= 2:
            x /= 2
            k += 1
        lo, hi = reduced_log_bounds(x)
        lower += mass*(k+lo/ln2_hi)
        upper += mass*(k+hi/ln2_lo)
    return lower, upper


def check_entropy_rate():
    r = Fraction(1, 36)
    scale = 10**12
    root = isqrt(35*scale**2)
    p_lo = Fraction(1, 2) - Fraction(root+1, 36*scale)
    p_hi = Fraction(1, 2) - Fraction(root, 36*scale)
    h_lo, h_hi = entropy_bounds(r)
    delta_lo, delta_hi = 1/(2*(1+h_hi)), 1/(2*(1+h_lo))
    # Entropy is increasing up to one half. These bounds round outwards.
    assert 0 < p_lo < p_hi < Fraction(1, 2)
    assert Fraction(1, 2) - (1-p_hi)*delta_lo < Fraction(219245, 10**6)
    assert 1 - (2-entropy_bounds(p_lo)[0])*delta_hi > Fraction(5438, 10**4)


def odd_prime(n):
    return n > 2 and all(n % k for k in range(2, isqrt(n) + 1))


def max_factor_count(order, least_prime):
    count = 0
    while order >= least_prime:
        order //= least_prime
        count += 1
    return count


def extension_tails(free, parity):
    tails = [0] * (free + 2)
    for k in range(free, -1, -1):
        tails[k] = tails[k + 1]
        if k % 2 == parity:
            tails[k] += comb(free, k)
    return tails


def overweight_extensions(free, block, ones, cutoff):
    """Count overweight odd-weight extensions for one fixed subset of size ones."""
    odd_tails = extension_tails(free, 1)
    total = 0
    for overlap in range(max(0, 2 * ones - block), ones + 1):
        fixed_weight = 2 + 2 * (ones - overlap)
        first_bad = min(free + 1, max(0, cutoff + 1 - fixed_weight))
        pairs = comb(ones, overlap) * comb(block - ones, ones - overlap)
        total += pairs * odd_tails[first_bad]
    return total


def polynomial_lower_bound(n, block, ones, cutoff, prime_count):
    """Use the prime-degree sieve with an upper bound on the distinct prime count."""
    if not odd_prime(n):
        raise ValueError("the degree must be an odd prime")
    if not 0 <= ones <= block or not 0 < 2 * block < n:
        raise ValueError("invalid block or subset size")
    order = (1 << n) - 1
    least_prime = 2 * n + 1
    dimension = 2 * block
    subsets = comb(block, ones)
    bad = overweight_extensions(n - 1 - dimension, block, ones, cutoff)
    root_upper = 1 + isqrt(order)
    main = (least_prime - prime_count) * order * subsets
    cost = (prime_count + 1) * dimension * root_upper + n * bad
    denominator = least_prime * (1 << dimension)
    return max(0, (main - denominator * cost) // (denominator * n))


def krawtchouk_row(block, weight, radius):
    """Coefficients through radius of (1 - z)^weight (1 + z)^(block - weight)."""
    row = [1]
    for j in range(radius):
        numerator = (block - 2 * weight) * row[j]
        if j:
            numerator -= (block - j + 1) * row[j - 1]
        value, remainder = divmod(numerator, j + 1)
        assert remainder == 0
        row.append(value)
    return row


def paired_factor_bound(block, free, cutoff, squared, overweight):
    """Sieve the overweight words by irreducibles through degree eleven using two intersections."""
    small = (2, 3, 3, 4, 4, 4)
    delta = prod(1-Fraction(1, 2**e) for e in small)
    # There are c_e monic irreducibles of degree e, with sum_{d|e} d*c_d = 2^e.
    counts = {}
    for e in range(1, 12):
        counts[e] = (2**e-sum(d*c for d, c in counts.items() if e % d == 0))//e
    hits = [Fraction(1, 2**e) for e, c in counts.items() if e >= 5 for _ in range(c)]
    mean = sum(hits)
    constant = delta*(1-mean+(mean**2-sum(x*x for x in hits))/2)
    fourier_mass = 2**len(small)*delta*(1+len(hits)+comb(len(hits), 2))

    length = sum(small)+2*11+1
    error = character_error(block, free, cutoff, squared, length)
    return ceil(constant*overweight + fourier_mass*error)


def character_error(block, free, cutoff, squared, length, two_ends=False):
    """Upper bound per unit of nonconstant Fourier mass for moduli of degree < length."""
    lower = block//length
    if two_ends:
        lower = min(a//length + (block-a)//length for a in range(block+1))
    middle = [krawtchouk_row(block, u, block) for u in range(lower, block//2+1)]
    middle_max = [max(map(abs, column)) for column in zip(*middle)]
    first = [min(free+1, max(0, cutoff-1-i)) for i in range(block+1)]
    first = [k+(1-i-k) % 2 for i, k in enumerate(first)]
    free_max = [0]*(block+1)
    for v in range(free//length, free//2+1):
        tail = krawtchouk_row(free, v, free) + [0, 0]
        for k in range(free, -1, -1):
            tail[k] += tail[k+2]
        free_max = [max(previous, abs(tail[k])) for previous, k in zip(free_max, first)]
    return sum(a*b*c for a, b, c in zip(squared, middle_max, free_max))


def selberg_constants(z):
    """Constant coefficient and absolute Fourier mass bound for squarefree divisors."""
    counts = {}
    for d in range(1, z+1):
        counts[d] = (2**d - sum(j*c for j, c in counts.items() if d % j == 0))//d

    def sum_products(numerator):
        coeff = [Fraction(1)] + [Fraction(0)]*z
        for d in range(2, z+1):
            norm = 2**d
            weight = Fraction(numerator(norm), norm-1)
            choices = [comb(counts[d], k)*weight**k for k in range(min(counts[d], z//d)+1)]
            coeff = [sum(val*coeff[i-k*d] for k, val in enumerate(choices[:i//d+1]))
                     for i in range(z+1)]
        return sum(coeff)

    g = sum_products(lambda norm: 1)
    absolute = sum_products(lambda norm: 1+norm)/g
    return 1/g, absolute**2


def fourier_count(n, block, radius, base, cutoff, prime_count, paired=False):
    """Count primitive polynomials using the radial Fourier weights and the small-factor sieve."""
    if not 0 <= radius <= block or base < 1:
        raise ValueError("invalid frequency radius or base")
    frequency = [
        isqrt(base**(2 * (radius - j)) * (factorial(radius) // factorial(radius - j)))
        for j in range(radius + 1)
    ]
    return frequency_count(n, block, frequency, cutoff, prime_count, paired=paired)


def frequency_count(n, block, frequency, cutoff, prime_count, *, paired=False, selberg=None, two_ends=False):
    if not odd_prime(n) or n <= (selberg or (11 if paired else 4)):
        raise ValueError("the prime degree must exceed the degree of every sieve factor")
    if not 0 < 2*block < n or not 1 <= len(frequency) <= block+1 or min(frequency) < 0 or not any(frequency):
        raise ValueError("invalid coefficient block or Fourier frequencies")
    if selberg is not None and (selberg < 2 or paired):
        raise ValueError("choose one small-factor sieve with degree at least two")
    if two_ends and selberg is None:
        raise ValueError("the two-ended count uses the squarefree-divisor sieve")
    free = n - 1 - 2 * block
    radius = len(frequency)-1
    maximum = sum(comb(block, j) * g for j, g in enumerate(frequency))**2
    tails = [extension_tails(free, parity) for parity in (0, 1)]
    mass = 0
    overweight = 0
    squared = []
    for i in range(block + 1):
        transform = sum(g * k for g, k in zip(frequency, krawtchouk_row(block, i, radius)))
        squared.append(transform**2)
        weight_mass = comb(block, i) * transform**2
        mass += weight_mass
        first_bad = min(free + 1, max(0, cutoff - 1 - i))
        overweight += weight_mass * tails[1 - i % 2][first_bad]
    assert mass == (1 << block) * sum(comb(block, j) * g*g for j, g in enumerate(frequency))

    if selberg is not None:
        constant, absolute = selberg_constants(selberg)
        error = character_error(block, free, cutoff, squared, 2*selberg+1, two_ends)
        bad = ceil(constant*overweight + absolute*error)
    elif paired:
        bad = paired_factor_bound(block, free, cutoff, squared, overweight)
    else:
        # The six irreducibles of degrees 2, 3 and 4 give a modulus of degree 20.
        degrees = (2, 3, 3, 4, 4, 4)
        residue_count = 1 << sum(degrees)
        unit_count = prod((1 << e) - 1 for e in degrees)
        min_weight = free // (sum(degrees) + 1)
        error_bits = (comb(free, min_weight).bit_length() - 1) // 2
        error_denominator = 1 << error_bits
        bad = (unit_count * overweight + residue_count - 1) // residue_count
        error_numerator = mass << (free + len(degrees))
        bad += (error_numerator + error_denominator - 1) // error_denominator

    order = (1 << n) - 1
    least_prime = 2 * n + 1
    denominator = least_prime << (2 * block)
    main = (least_prime - prime_count) * order * mass
    cost = (prime_count + 1) * (2 * block) * (isqrt(order) + 1) * maximum + n * bad
    return max(0, (main - denominator * cost) // (denominator * n * maximum))


def main():
    check_entropy_rate()
    # These inequalities give the strict decimal bound on the asymptotic coefficient.
    assert 7**462 < 2**1297
    assert 713 * 5000 < 1159 * 3076
    assert 37**13209 < 2**2368 * 36**12852
    assert 13661 * 4000 < 877 * 62308

    n = 1229
    elementary_count = max_factor_count((1 << n) - 1, 2 * n + 1)
    assert elementary_count == 109
    # The separate cofactor theorem in the note proves the second upper bound, 4 + 15.
    cases = [(411, 54, 329, elementary_count, 619), (414, 55, 327, 19, 613)]
    for block, ones, cutoff, count, exponent in cases:
        bound = polynomial_lower_bound(n, block, ones, cutoff, count)
        assert bound > 2**exponent
        print(f"degree {n}, weight <= {cutoff}, at most {count} order primes")
        print(f"  at least {bound} primitive polynomials (> 2^{exponent})")

    # The i-th distinct order prime is at least 2*n*i + 1.
    assert prod(2*n*i + 1 for i in range(1, 78)) > (1 << n) - 1
    for block, radius, base, cutoff, count, exponent, paired in [
        (502, 16, 14, 315, 76, 621, False), (509, 15, 14, 313, 19, 616, False),
        (510, 14, 14, 313, 76, 622, True), (503, 16, 13, 311, 19, 619, True),
    ]:
        bound = fourier_count(n, block, radius, base, cutoff, count, paired)
        assert bound > 2**exponent
        print(f"degree {n}, weight <= {cutoff}, at most {count} order primes")
        print(f"  at least {bound} primitive polynomials (> 2^{exponent})")

    # A radial frequency vector for the squarefree-divisor sieve.
    frequency = [87562546122, 22856382314, 5849044663, 1460837027, 354444590, 83157868,
                 18776391, 4059835, 835957, 162853, 29770, 5050, 783, 108, 13, 1]
    bound = frequency_count(n, 508, frequency, 309, 19, selberg=20)
    assert bound > 2**616
    print(f"degree {n}, weight <= 309, at least {bound} primitive polynomials (> 2^616)")
    bound = frequency_count(n, 508, frequency, 309, 19, selberg=19, two_ends=True)
    assert bound > 2**616
    print(f"all 509 divisions of 508 prescribed end coefficients, at least {bound} (> 2^616)")


if __name__ == "__main__":
    main()
