"""Verify a degree-independent certificate for X^(2^s) + (1+X^2)(1+X^3)."""

from dataclasses import dataclass

from check_exterior import fixed_dimension
from make_witnesses import gcd, remainder


def laurent_product(left, right):
    """A binary Laurent polynomial is the set of its signed exponents."""
    result = set()
    for exponent in left:
        result.symmetric_difference_update(exponent + j for j in right)
    return frozenset(result)


ONE = frozenset({0})
T = frozenset({1})
EMPTY = frozenset()
D = frozenset({0, -5})  # 1 + t^-5


@dataclass(frozen=True)
class Quadratic:
    """a + bz over F2[t,t^-1], with z^2 = z + 1 + t^-5."""

    a: frozenset
    b: frozenset

    def __add__(self, other):
        return Quadratic(self.a ^ other.a, self.b ^ other.b)

    def __mul__(self, other):
        bd = laurent_product(self.b, other.b)
        return Quadratic(
            laurent_product(self.a, other.a) ^ laurent_product(D, bd),
            laurent_product(self.a, other.b) ^ laurent_product(self.b, other.a) ^ bd,
        )

    def norm(self):
        return (laurent_product(self.a, self.a) ^ laurent_product(self.a, self.b)
                ^ laurent_product(D, laurent_product(self.b, self.b)))


def image_symmetric(u, v, zero, one):
    """Elementary symmetric functions after applying h to the roots of X³+uX²+vX+1."""
    def shift(column):
        a, b, c = column
        return c, a + v*c, b + u*c

    power = (one, zero, zero)
    column = (zero, zero, zero)
    for exponent in range(6):
        if exponent in (0, 2, 3, 5):
            column = tuple(x + y for x, y in zip(column, power))
        power = shift(power)

    # Multiplication by h on the basis 1, X, X². The coefficients of its
    # characteristic polynomial work for repeated roots as well.
    (a, d, g), (b, e, h), (c, f, i) = column, shift(column), shift(shift(column))
    return (a + e + i, a*e + b*d + a*i + c*g + e*i + f*h,
            a*e*i + b*f*g + c*d*h + a*f*h + b*d*i + c*e*g)


def normalize(poly):
    offset = min(poly)
    return offset, sum(1 << (i - offset) for i in poly)


def check_certificate():
    from sympy import GF
    from sympy.polys.rings import ring

    binary, u, v = ring("u,v", GF(2))
    _, _, product = image_symmetric(u, v, binary.zero, binary.one)
    t = u + v
    if product != t**3 * (t**2 + u*v):
        raise ArithmeticError("incorrect cubic product identity")

    zero, one = Quadratic(EMPTY, EMPTY), Quadratic(ONE, EMPTY)
    u, v = Quadratic(EMPTY, T), Quadratic(T, T)  # tz, t(z+1)
    norms = []
    for step in range(3):
        u, v, product = image_symmetric(u, v, zero, one)
        defect = product + one
        if step == 0:
            if defect != zero:
                raise ArithmeticError("the parameterization must satisfy the first equation")
        else:
            norms.append(normalize(defect.norm()))

    (offset1, n1), (offset2, n2) = norms
    residue = remainder(n2, n1)
    if gcd(n1, n2) != 1:
        raise ArithmeticError("the two norms have a common factor")
    print(f"Norms have least exponents {offset1}, {offset2} and normalized degrees "
          f"{n1.bit_length()-1}, {n2.bit_length()-1}.")
    print(f"N1 = {n1:#x}, N2 mod N1 = {residue:#x}, gcd = 1.")


if __name__ == "__main__":
    check_certificate()
    for degree, dilation in [(8, 1), (16, 1), (24, 3), (32, 1)]:
        taps = [i*dilation for i in (0, 2, 3, 5)]
        if any(fixed_dimension(degree, taps, k) for k in (1, 2, 3)):
            raise ArithmeticError(f"exterior-power disagreement in degree {degree}")
    print("Checked exterior powers 1, 2, 3 directly in degrees 8, 16, 24, 32.")
