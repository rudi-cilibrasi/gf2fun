"""Exclude product-one quartets for X^(2^s)+(1+X²)(1+X³). Requires python-flint."""

from flint import nmod_mpoly_ctx, nmod_poly

from check_quartic_period import (MUL, ONE, defect, image_coefficients, monomial,
                                  normalize_p, unit_power, univariate_remainder)


def symmetric_forms():
    """Reconstruct the four binary coefficient polynomials from the quartic matrix."""
    ctx = nmod_mpoly_ctx.get(("u", "v", "w"), 2)
    u, v, w = ctx.gens()
    one = ctx.constant(1)
    forms = (*image_coefficients(u, v, w, zero=ctx.constant(0), one=one),
             defect(u, v, w, one=one))
    if any(f.total_degree() != 5 for f in forms):
        raise ArithmeticError("unexpected degree for the image coefficients")
    return [list(f.monoms()) for f in forms]


class Surface:
    """Pairs represent f₀ + A f₁ over F₂[t,B], where A² = AB+B²+t."""

    def __init__(self):
        self.ctx = nmod_mpoly_ctx.get(("t", "B"), 2)
        self.t, self.b = self.ctx.gens()
        self.relation = self.b**2 + self.t
        self.zero = self.ctx.constant(0)
        self.one = self.ctx.constant(1)

    def multiply(self, x, y):
        bd = x[1]*y[1]
        return (x[0]*y[0] + self.relation*bd,
                x[0]*y[1] + x[1]*y[0] + self.b*bd)

    def powers(self, x):
        def square(y):
            e = y[1]**2
            return y[0]**2 + self.relation*e, self.b*e
        two = square(x)
        four = square(two)
        return [(self.one, self.zero), x, two, self.multiply(two, x), four, self.multiply(four, x)]

    def evaluate(self, forms, coordinates, denominator):
        """Evaluate the degree-five homogenizations, sharing their monomials."""
        powers = [self.powers(x) for x in coordinates]
        denominators = [denominator**i for i in range(6)]
        terms = {}
        outputs = []
        for form in forms:
            a, b = self.zero, self.zero
            for i, j, k in form:
                if (i, j, k) not in terms:
                    pair = self.multiply(powers[0][i], powers[1][j])
                    c, d = self.multiply(pair, powers[2][k])
                    scale = denominators[5-i-j-k]
                    terms[i, j, k] = c*scale, d*scale
                c, d = terms[i, j, k]
                a, b = a+c, b+d
            outputs.append((a, b))
        return outputs

    def remove_t(self, f):
        """t is nonzero on the surface. B may be zero."""
        t_order, _ = f.term_content().monoms()[0]
        return f // self.t**t_order

    def norm(self, x):
        a, b = x
        return self.remove_t(a**2 + self.b*a*b + self.relation*b**2)

    def cross(self, x, y):
        return self.remove_t(x[0]*y[1] + x[1]*y[0])

    def resultant(self, f, g):
        eliminated = self.remove_t(f.resultant(g, 1))
        coefficients = [0] * (int(eliminated.degrees()[0]) + 1)
        for (i, j), coefficient in eliminated.terms():
            if j:
                raise ArithmeticError("the resultant still depends on B")
            coefficients[i] = int(coefficient)
        return nmod_poly(coefficients, 2)


def restrict_parameter():
    surface = Surface()
    t, b, zero, one = surface.t, surface.b, surface.zero, surface.one
    forms = symmetric_forms()
    # t = u+v+w, A = t²(u+v+1), B = t²(v+w+1).
    # The common denominator in the following coordinates is t².
    coordinates = [(t**3+t**2+b, zero), (t**3+b, one), (t**3+t**2, one)]
    denominator = t**2
    if surface.evaluate(forms[-1:], coordinates, denominator) != [(zero, zero)]:
        raise ArithmeticError("initial product defect must vanish")
    coordinates = surface.evaluate(forms[:3], coordinates, denominator)
    denominator **= 5
    defects = []
    for step in range(1, 4):
        if step < 3:
            *coordinates, value = surface.evaluate(forms, coordinates, denominator)
            denominator **= 5
        else:
            value, = surface.evaluate(forms[-1:], coordinates, denominator)
        defects.append(value)

    first, second, third = defects
    norm = surface.norm(first)
    equations = (surface.cross(first, second), surface.norm(second), surface.cross(first, third))
    common = None
    for equation in equations:
        eliminated = surface.resultant(norm, equation)
        common = eliminated if common is None else common.gcd(eliminated)
        print(f"Eliminant degree {eliminated.degree()}, common degree {common.degree()}.", flush=True)
    cube = nmod_poly([1, 0, 0, 1], 2)
    if common != cube * nmod_poly([1, 1], 2)**4:
        raise ArithmeticError("unexpected common eliminant")


def remaining_quartics():
    """At t³=1, determine p from two univariate gcds on the Laurent surface."""
    omega = unit_power(2, 5)
    omega2 = MUL[omega][omega]
    def coordinates(t, p, q):
        b = p + q
        a = monomial(coefficient=omega2)*p + monomial(coefficient=omega)*q
        return t+b+ONE, t+a+b, t+a+ONE

    survivors = []
    for t in (1, omega, omega2):
        t0 = monomial(coefficient=t)
        uvw = coordinates(t0, monomial(p=1), monomial(p=-1))
        first = image_coefficients(*uvw)
        second = image_coefficients(*first)
        left, right = normalize_p(defect(*first)), normalize_p(defect(*second))
        while right:
            left, right = right, univariate_remainder(left, right)
        inverse = unit_power(left[max(left)], -1)
        common = {i: MUL[c][inverse] for i, c in left.items()}
        # In the first case the monic gcd is (p+1)²(p+omega).
        expected = {0: omega, 1: 1, 2: omega, 3: 1} if t == 1 else {0: omega2, 1: 1}
        if common != expected:
            raise ArithmeticError(f"unexpected p-polynomial at t={t}")
        for p in ((1, omega) if t == 1 else (omega2,)):
            uvw = coordinates(t0, monomial(coefficient=p),
                              monomial(coefficient=unit_power(p, -1)))
            image = image_coefficients(*uvw)
            survivors.append((tuple(v.get((0, 0), 0) for v in uvw),
                              tuple(v.get((0, 0), 0) for v in image)))
    expected = [((0,0,1), (1,0,0)), ((1,0,0), (0,0,1)),
                ((omega,)*3, (omega2,)*3), ((omega2,)*3, (omega,)*3)]
    if survivors != expected:
        raise ArithmeticError("unexpected quartic or image")
    print("Four quartics remain. Two binary quartics are exchanged; the others are reciprocal.")


if __name__ == "__main__":
    restrict_parameter()
    remaining_quartics()
