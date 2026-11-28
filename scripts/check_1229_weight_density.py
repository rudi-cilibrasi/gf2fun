"""Bound the ordinary fraction of nonprimitive survivors in any window of 680 possible taps."""

from fractions import Fraction
from math import ceil, floor, isqrt, prod

from check_primitive_weight_bound import frequency_statistics


N = 1229
FIXED = 548
ORDER = 2**N - 1
ROOT_BOUND = isqrt(ORDER) + 1
PRIMES = (36871, 46703, 10543179280661916121033, 9536289355314392579996071515160583098298616686033085857)
INDEX_FLOOR = 818085338814611458

# Cutoff, Fourier coefficients by radius, count exponent and strict upper failure fraction.
CASES = (
    (313, [338258387341, 50052925585, 6895969111, 874342382, 100279148, 10121411, 854553, 52701, 100],
     619, Fraction(29, 100)),
    (315, [1312773419, 185773167, 24377617, 2927119, 315242, 29457, 2229, 100],
     622, Fraction(37, 1000)),
    (319, [185918844, 23803765, 2788558, 293226, 26826, 2009, 100], 627, Fraction(1, 1000)),
    (325, [39562098, 4303710, 417529, 34924, 2356, 100], 634, Fraction(1, 100000)),
    (345, [94296071, 4797761, 160903, 100], 653, Fraction(14, 10**12)),
    (375, [1], 670, Fraction(13, 10**17)),
)


def main():
    cofactor, rem = divmod(ORDER, prod(PRIMES))
    if rem or cofactor >= INDEX_FLOOR**16 or sum(Fraction(1, p) for p in PRIMES) >= Fraction(1, 20000):
        raise ArithmeticError("the known-part or residual-prime estimate failed")
    # Count field elements in each residual prime-index subgroup in the entire window.
    numerator = 15 * (Fraction(ORDER, INDEX_FLOOR << FIXED) + FIXED*ROOT_BOUND)
    upper = ceil(numerator/N)
    for cutoff, frequency, exponent, risk in CASES:
        peak, mass, bad = frequency_statistics(N, FIXED, frequency, cutoff, selberg=20, two_ends=True)
        main_term = Fraction(19999*ORDER*mass, 20000 << (2*FIXED))
        # The four known prime exclusions and the unrestricted field count cost five errors.
        lower = floor((main_term - 5*2*FIXED*ROOT_BOUND*peak - N*bad)/(N*peak))
        if lower <= 2**exponent or upper >= risk*lower:
            raise ArithmeticError(f"the claimed population or fraction failed at weight {cutoff}")
        print(f"At most {cutoff} terms: more than 2^{exponent} survivors, "
              f"fraction nonprimitive < {risk}.")


if __name__ == "__main__":
    main()
