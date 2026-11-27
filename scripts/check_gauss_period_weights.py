"""Classify five-term projective images of binary optimal normal basis generators."""

from sympy import isprime

from make_witnesses import prime_factors, x_power


def translate(mask):
    """Evaluate a packed binary polynomial at X+1 by Horner's rule."""
    value = 0
    for bit in reversed(range(mask.bit_length())):
        value = value ^ (value << 1) ^ ((mask >> bit) & 1)
    return value


def charts(mask, degree):
    reciprocal = int(f"{mask:0{degree+1}b}"[::-1], 2)
    return mask, translate(mask), translate(reciprocal)


def weights(n):
    """The weight recurrences in the three charts, read from the high bit down."""
    # In each tuple the first entry counts the terms of the projective form.
    # The remaining entries follow the order of the three recurrences in the note.
    t, v, u = 1, 0, 1
    s, a, b = 1, 1, 0
    r, l, c, d, e = 1, 1, 0, 0, 1
    for digit in bin(n)[2:]:
        if digit == "0":
            t, v, u = t+v, v, t
            s, a, b = a+b, s, 2*b
            r, l, c, d, e = l+c, r+c, c, 2*c, r
        else:
            t, v, u = t+u, t, u
            s, a, b = a+b, 2*a, s
            r, l, c, d, e = d+r, e+r, r, 2*r, e
    return t, s, r


def order(mask, n):
    size = (1 << n)-1
    if x_power(size, mask) != 1:
        raise ArithmeticError(f"full power failed for {mask:#x}")
    for p in set(prime_factors(size)):
        while size % p == 0 and x_power(size//p, mask) == 1:
            size //= p
    return size


def full_period_orbit(n):
    p = 2*n+1
    if not isprime(p):
        return False
    powers = (pow(2, k, p) for k in range(n))
    return len({min(r, p-r) for r in powers}) == n


def main():
    expected = ((1, 2, 3, 4, 5, 6, 7, 8, 15),
                (1, 2, 3, 4, 5, 6, 7, 10, 11, 12, 13),
                (1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 16, 24))
    sparse = [[], [], []]
    primitive = set()
    orders = {}
    before, current = 1, 3
    # The proved bit-length bound excludes n >= 32. Continue farther to
    # cross-check the digit recurrence against all three polynomials directly.
    for n in range(1, 513):
        forms = charts(current, n)
        counts = tuple(f.bit_count() for f in forms)
        if counts != weights(n) or min(counts) < 2*(n.bit_length()//2)+1:
            raise ArithmeticError(f"weight recurrence or dyadic bound failed at {n}")
        if (n & (n-1)) == 0 and min(counts) != 2*(n.bit_length()//2)+1:
            raise ArithmeticError(f"equality failed at the dyadic endpoint {n}")
        for i, (f, count) in enumerate(zip(forms, counts, strict=True)):
            if count > 5:
                continue
            sparse[i].append(n)
            if n > 1 and full_period_orbit(n):
                value = order(f, n)
                orders[n, i] = value
                if value == (1 << n)-1:
                    primitive.add(n)
        before, current = current, (current << 1) ^ before
    if tuple(map(tuple, sparse)) != expected or primitive != {2, 3, 5, 6, 9, 11}:
        raise ArithmeticError("unexpected type-II classification")
    if {key: value for key, value in orders.items() if value != (1 << key[0])-1} != {(6, 1): 21}:
        raise ArithmeticError("unexpected nonprimitive sparse image")

    # The type-I proof leaves only conductors 3 and 5. Their cyclotomic
    # polynomials consist entirely of ones before changing coordinates.
    type_one = set()
    for p in (3, 5):
        for f in charts((1 << p)-1, p-1):
            if f.bit_count() <= 5 and order(f, p-1) == (1 << (p-1))-1:
                type_one.add(p-1)
    if type_one != {2, 4}:
        raise ArithmeticError("unexpected type-I classification")
    for i, degrees in enumerate(sparse):
        print(f"Period chart {i+1}, all degrees with weight at most five: {degrees}.")
    print(f"Primitive images in degree greater than one: {sorted(type_one | primitive)}.")


if __name__ == "__main__":
    main()
