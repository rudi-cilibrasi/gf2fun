"""Count or export split Hermitian relations for linear norms in a height-two model."""

import argparse
import gzip
import json
from collections import Counter

from check_1229_height_two import CERTIFICATE, Q, binary_polynomial, bits, quadratic_constants, scalar


EXPECTED = {(3, 1019): (698712, 680), (6, 246): (698021, 688), (6, 285): (698704, 688),
            (6, 454): (698704, 688), (7, 88): (698021, 688)}


def real_parameters(u, v, audit=False):
    """The cubic for a real center splits over the quadratic constants iff it has a real root."""
    powers = []
    z = 1
    for _ in range(Q-1):
        powers.append(z)
        z <<= 1
        if z & Q:
            z ^= 0x409
    if z != 1 or len(set(powers)) != Q-1:
        raise ArithmeticError("invalid ten-bit constant field")
    logs = [0]*Q
    for i, z in enumerate(powers):
        logs[z] = i
    powers += powers
    def mul(a, b):
        return powers[logs[a]+logs[b]] if a and b else 0
    all_radii = (1 << Q)-1
    radii = [0]*Q
    radii[0] = all_radii  # At zero center the substituted polynomial always has degree at most two.
    traces = 0
    for t in range(Q):
        denominator = mul(t, t)^t^v
        if not denominator:
            radii[t] = all_radii  # These are the two possible poles of R.
            continue
        y = mul(u, powers[Q-1-logs[denominator]])
        slope, offset = t^y, mul(t, y)
        traces |= 1 << slope
        for b in range(Q):
            radii[b] |= 1 << (offset^mul(b, slope))
    radii = [mask & ~(1 << mul(b, b)) for b, mask in enumerate(radii)]
    if audit:
        # Independently classify every monic cubic by translating it to Y^3+pY+h.
        possible = [0]*Q
        for y in range(Q):
            cube = mul(mul(y, y), y)
            for p in range(Q):
                possible[p] |= 1 << (cube ^ mul(p, y))
        def has_root(a, b, c):
            return (possible[mul(a, a)^b] >> (mul(a, b)^c)) & 1
        for b in range(1, Q):
            inv = powers[Q-1-logs[b]]
            verified = 0
            for d in range(Q):
                if d == mul(b, b):
                    continue
                a1, b1 = mul(b^d, inv), mul(u^mul(b, v)^d, inv)
                c1 = mul(mul(u, b)^mul(d, v), inv)
                verified |= has_root(a1, b1, c1) << d
            if verified != radii[b]:
                raise ArithmeticError("cubic test differs from the norm-circle incidence count")
        trace_cubics = sum(has_root(1^d, v^d, mul(d, v)^u) << d for d in range(Q))
        if radii[0] != (all_radii ^ 1) or trace_cubics != traces:
            raise ArithmeticError("incorrect zero-center or trace-line incidence count")
    if (sum(mask.bit_count() for mask in radii), traces.bit_count()) != EXPECTED[u, v]:
        raise ArithmeticError("the split relation count differs from the published census")
    return radii, traces


def export_row(record, model, center, d_mask):
    field, ring = quadratic_constants()
    t = ring.gen()
    theta = scalar(record["constant_generator_in_quadratic_extension"], field)
    def real(mask):
        return binary_polynomial(mask, ring)(theta)
    u, v, d = real(model["u"]), real(model["v"]), real(d_mask)
    h1 = t**2+t+v
    if center is None:
        numerator = u+(t+d)*h1
        source = t**Q+t+d
        epsilon = field.gen()/(field.gen()+field.gen()**Q)
        points = [epsilon*d+real(i) for i in range(Q)]
    else:
        b = real(center)
        rho = d+b*b
        if not rho:
            raise ValueError("this radius gives a singular form")
        numerator = (t+b)*u+(b*t+d)*h1
        source = t**(Q+1)+b*t+b*t**Q+d
        radius = rho**(Q//2)
        generator = field.gen()**(Q-1)
        points = [b+radius*generator**i for i in range(Q+1)]
    polynomial = ring.one()
    for z in points:
        polynomial *= t+z
    if polynomial != source:
        raise ArithmeticError("the finite points do not reconstruct the projective source")
    def key(z):
        return min(bits(z), bits(z**Q))
    coefficients = Counter(key(z) for z in points)
    for poly, sign in ((h1, 1), (numerator, -1)):
        for factor, mult in poly.factor()[1]:
            if factor.degree() != 1:
                raise ArithmeticError("the substituted polynomial has a nonlinear factor")
            coefficients[key(factor[0])] += Q*sign*mult
    # Replay the source, substitution, and denominator in the certified degree-1229 quotient over k.
    packed = int(model["relative_modulus_packed_hex"], 16)
    g = ring([real((packed >> (10*i)) & 1023) for i in range(1230)])
    y = t**Q
    if (h1.compose_mod(y, g)*source - numerator.compose_mod(y, g)) % g != 0:
        raise ArithmeticError("incorrect cleared Frobenius identity")
    return {"model": [model["u"], model["v"]], "center": center, "d": d_mask,
            "finite_source_points": len(points), "substituted_degree": numerator.degree(),
            "relation": [[hex(c), k] for c, k in sorted(coefficients.items()) if k]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=int, nargs=2, metavar=("U", "V"))
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--pencil", type=int, nargs=2, metavar=("B", "D"), help="export one norm-circle equation")
    group.add_argument("--trace", type=int, metavar="D", help="export one trace-line equation")
    group.add_argument("--parameters", action="store_true", help="list all split (family,b,d) identifiers in one model")
    parser.add_argument("--audit", action="store_true", help="independently test the cubic for every parameter")
    args = parser.parse_args()
    with gzip.open(CERTIFICATE, "rt") as stream:
        record = json.load(stream)
    selected = args.model or ([3, 1019] if args.parameters or args.pencil is not None or args.trace is not None else None)
    models = [r for r in record["models"] if not selected or [r["u"],r["v"]] == selected]
    if not models:
        parser.error("unrecognized height-two model")
    for r in models:
        radii, traces = real_parameters(r["u"], r["v"], args.audit)
        if args.parameters:
            print("family,b,d")
            for b, mask in enumerate(radii):
                for d in range(Q):
                    if mask >> d & 1:
                        print(f"norm,{b},{d}")
            for d in range(Q):
                if traces >> d & 1:
                    print(f"trace,,{d}")
            continue
        if args.pencil is None and args.trace is None:
            circles = sum(group.bit_count() for group in radii)
            print(f"u={r['u']}, v={r['v']}: {circles:,} split norm circles and {traces.bit_count():,} "
                  f"split trace lines, totaling {circles+traces.bit_count():,} equations.")
            continue
        b, d = args.pencil if args.pencil is not None else (None, args.trace)
        if not 0 <= d < Q or b is not None and not 0 <= b < Q:
            parser.error("parameters must be ten-bit constants")
        if not ((traces if b is None else radii[b]) >> d & 1):
            parser.error("the specified pencil is singular or has a nonsplit substitution")
        print(json.dumps(export_row(record, r, b, d), indent=2))


if __name__ == "__main__":
    main()
