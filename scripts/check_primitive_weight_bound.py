"""Check the exact polynomial counts in the primitive-weight bound for degree 1229."""

from math import comb, isqrt


def max_factor_count(order, least_prime):
    count = 0
    while order >= least_prime:
        order //= least_prime
        count += 1
    return count


def overweight_extensions(free, block, ones, cutoff):
    """Count overweight odd-weight extensions for one fixed subset of size ones."""
    odd_tails = [0] * (free + 2)
    for k in range(free, -1, -1):
        odd_tails[k] = odd_tails[k + 1]
        if k % 2:
            odd_tails[k] += comb(free, k)

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


if __name__ == "__main__":
    main()
