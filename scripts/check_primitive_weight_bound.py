"""Check the exact polynomial counts in the primitive-weight bound for degree 1229."""

from math import comb, factorial, isqrt, prod


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
    if n <= 2 or any(n % k == 0 for k in range(2, isqrt(n) + 1)):
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


def fourier_count(n, block, radius, base, cutoff, prime_count):
    """Count primitive polynomials using the radial Fourier weights and the small-factor sieve."""
    free = n - 1 - 2 * block
    frequency = [
        isqrt(base**(2 * (radius - j)) * (factorial(radius) // factorial(radius - j)))
        for j in range(radius + 1)
    ]
    maximum = sum(comb(block, j) * g for j, g in enumerate(frequency))**2
    tails = [extension_tails(free, parity) for parity in (0, 1)]
    mass = 0
    overweight = 0
    for i in range(block + 1):
        transform = sum(g * k for g, k in zip(frequency, krawtchouk_row(block, i, radius)))
        weight_mass = comb(block, i) * transform**2
        mass += weight_mass
        first_bad = min(free + 1, max(0, cutoff - 1 - i))
        overweight += weight_mass * tails[1 - i % 2][first_bad]
    assert mass == (1 << block) * sum(comb(block, j) * g*g for j, g in enumerate(frequency))

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
    for block, radius, base, cutoff, count, exponent in [
        (502, 16, 14, 315, 76, 621), (509, 15, 14, 313, 19, 616)
    ]:
        bound = fourier_count(n, block, radius, base, cutoff, count)
        assert bound > 2**exponent
        print(f"degree {n}, weight <= {cutoff}, at most {count} order primes")
        print(f"  at least {bound} primitive polynomials (> 2^{exponent})")


if __name__ == "__main__":
    main()
