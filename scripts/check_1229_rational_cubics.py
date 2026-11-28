"""Check two pentanomial roots whose powers are products of linear factors in a rational coordinate."""

import argparse
import json
from math import gcd

from check_1229_frobenius_models import primitive_generator_in
from check_degree_1229 import COFACTOR, GROUP, KNOWN, N, check_known_order
from check_factor_base import modulus
from check_sparse_root_models import X, inverse, irreducible_candidate, small_factors
from period_coordinate import mask_of


CASES = {256: (461, 167), 400: (29, 41)}


def taps(u, v):
    return tuple(sorted((u, 2*u, v)))


def census():
    small = small_factors()
    tested = []
    for v in range(1, N//3+1):
        u = N-3*v
        if 2*u < N and len(set(taps(u, v))) == 3:
            tested.append((u, v))
    hits = [(u, v) for u, v in tested if irreducible_candidate(taps(u, v), small)]
    if len(tested) != 205 or hits != [(u, v) for v, (u, _) in CASES.items()]:
        raise ArithmeticError("unexpected irreducibles in the rational cubic family")


def verify(v):
    u, weight = CASES[v]
    f = modulus(N, taps(u, v))
    check_known_order(f)
    if gcd(u, GROUP) != 1 or gcd(v, GROUP) != 1:
        raise ArithmeticError("a sparse-root power could lose part of its order")
    b, t = X**u, X**v
    w = (b+t)*inverse(t*t+t+1, f) % f
    if (w*w*(w+1) % f != b or (w*w+w+1+t*w) % f != 0
            or (w**5*(t+1)+b*b) % f != 0 or ((w+1)**5+b*(t+1)**2) % f != 0):
        raise ArithmeticError("the rational parametrization or its two fifth-power identities failed")
    quad = X*X+X+1
    g = X**(u+2*v)*(X+1)**v+quad**u
    if g.degree() != N or mask_of(g).bit_count() != weight or g.compose_mod(w, f) != 0:
        raise ArithmeticError("the rational coordinate has an incorrect modulus")
    # r=(r^u)^i (r^v)^j, where ui+vj=1. Negative powers use the subgroup order.
    i = pow(u, -1, v)
    j = (1-u*i)//v
    cubic = X*X*(X+1)
    ratio = quad*inverse(X, g) % g
    r = cubic.pow_mod(i, g)*ratio.pow_mod(j % GROUP, g) % g
    if (r.compose_mod(w, f) != X or f.compose_mod(r, g) != 0
            or r.pow_mod(u, g) != cubic or r.pow_mod(v, g) != ratio):
        raise ArithmeticError("the inverse coordinate or the two equal-order values failed")
    return g, cubic


def projected_task(v):
    field, cubic = verify(v)
    generator = primitive_generator_in(field)
    values = [p.pow_mod(KNOWN, field) for p in (generator, X, X+1, cubic)]
    return field, values


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--v", type=int, choices=CASES, help="export a projected cubic and its two linear factors")
    answers = parser.add_mutually_exclusive_group()
    answers.add_argument("--linear-logs", type=int, nargs=2, metavar=("LOG_W", "LOG_W_PLUS_1"))
    answers.add_argument("--cubic-log", type=int, metavar="EXPONENT")
    args = parser.parse_args()
    if args.v is None:
        if args.linear_logs is not None or args.cubic_log is not None:
            parser.error("select the pentanomial with --v when checking exponents")
        census()
        for v in CASES:
            verify(v)
        print("Checked all 205 supports, both irreducibles, their order projections and both changes of coordinate.")
        return

    u, _ = CASES[args.v]
    field, (base, w, successor, cubic) = projected_task(args.v)
    e = args.cubic_log
    if args.linear_logs is not None:
        for value, log in zip((w, successor), args.linear_logs):
            if not 0 <= log < COFACTOR or base.pow_mod(log, field) != value:
                raise ValueError("a submitted linear logarithm fails direct powering")
        a, b = args.linear_logs
        e = (2*a+b) % COFACTOR
    if e is not None:
        if not 0 <= e < COFACTOR or base.pow_mod(e, field) != cubic:
            raise ValueError("the submitted cubic logarithm fails direct powering")
        print(f"The pentanomial root has exact index {gcd(e, COFACTOR)} in the multiplicative group.")
    else:
        print(json.dumps({"taps": taps(u, args.v), "u": u, "v": args.v,
                          "modulus_hex": hex(mask_of(field)), "K": str(KNOWN), "C": str(COFACTOR),
                          "base_hex": hex(mask_of(base)), "w_projected_hex": hex(mask_of(w)),
                          "w_plus_1_projected_hex": hex(mask_of(successor)),
                          "cubic_projected_hex": hex(mask_of(cubic))}, indent=2))


if __name__ == "__main__":
    main()
