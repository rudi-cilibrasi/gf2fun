"""Construct a five-term candidate with a prescribed small-factor cutoff and certified period bound."""

import argparse
from math import gcd, lcm


def candidate(n, cutoff, w=1):
    if cutoff < 2 or w < 1 or w % 8 != 1 or gcd(w, n) != 1:
        raise ValueError("expected cutoff >= 2 and positive w = 1 mod 8 coprime to the degree")
    period = lcm(*(2**j-1 for j in range(1, cutoff+1)))
    if n < 64*(period+1)*w:
        raise ValueError(f"the construction needs degree at least {64*(period+1)*w} for these inputs")
    r = n % 8
    if r == 0:
        j = next(j for j in (1, 3) if (1+j*period) % 4 == 0)
        c = 2+2*j*period
        taps, width = [2*w, period*w, c*w], c
    elif r in (1, 7):
        taps, width = [8*w, 8*period*w, 8*(period+1)*w], period+1
    elif r in (3, 5):
        s = next(j*period for j in (1, 3, 5, 7) if (j*period+2) % 8 == r)
        u, v = s*w, n-(s+2)*w
        taps, width = [u, v, u+v], 2*s+2
    else:
        c = 4*period
        k = (6 if r == 2 else 4)*period+1
        taps, width = [c*w, k*w, n-c*w], c+k
    support = [0, *sorted(taps), n]
    if len(set(support)) != 5 or gcd(*support) != 1 or width > 14*period+2:
        raise ArithmeticError(f"inconsistent construction in degree {n}")
    return support, width


def audit():
    from flint import nmod_poly

    tested = 0
    for cutoff, w in ((2, 1), (3, 1), (2, 9)):
        period = lcm(*(2**j-1 for j in range(1, cutoff+1)))
        start = 64*(period+1)*w
        for residue in range(8):
            n = start+residue
            while gcd(n, w) != 1:
                n += 8
            support, _ = candidate(n, cutoff, w)
            coeffs = [0]*(n+1)
            for e in support:
                coeffs[e] = 1
            factors = nmod_poly(coeffs, 2).factor()[1]
            if len(factors) % 2 != 1 or any(g.degree() <= cutoff or e != 1 for g, e in factors):
                raise ArithmeticError(f"factorization disagrees in degree {n}, cutoff {cutoff}, w={w}")
            tested += 1
    print(f"Direct binary factorization verified squarefreeness, parity and the cutoff in {tested} cases.")


def primitive_examples():
    import json
    from math import prod
    from pathlib import Path

    from flint import fmpz, nmod_poly
    from check_product_range import prime_index_powers

    archive = Path(__file__).resolve().parents[1] / "data"
    tables = {
        "mersenne-2417-2560.json": [(2549, 2, 1), (2560, 3, 1)],
        "mersenne-2561-2688.json": [(2590, 2, 1), (2620, 2, 9)],
        "mersenne-2945-3072.json": [(2972, 2, 9)],
        "mersenne-4224-7560-extra.json": [(4224, 2, 1)],
    }
    x = nmod_poly([0, 1], 2)
    verified = set()
    for name, examples in tables.items():
        records = json.loads((archive / name).read_text())
        for n, cutoff, w in examples:
            support, _ = candidate(n, cutoff, w)
            f = sum((x**e for e in support), nmod_poly([], 2))
            factors = records[str(n)]
            order = 2**n-1
            primes = set(factors)
            if prod(factors) != order or not all(fmpz(p).is_prime() for p in primes-verified):
                raise ArithmeticError(f"incomplete group factorization in degree {n}")
            verified.update(primes)
            if x.pow_mod(order, f) != 1 or any(v == 1 for _, v in prime_index_powers(x, order, sorted(primes), f)):
                raise ArithmeticError(f"failed full-order test in degree {n}")
            print(f"Primitive in degree {n} with exponents {support}.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degree", nargs="?", type=int)
    parser.add_argument("--cutoff", type=int, default=2)
    parser.add_argument("--w", type=int, default=1, help="optional spacing multiplier, 1 modulo 8")
    parser.add_argument("--audit", action="store_true", help="factor examples in all eight degree classes")
    parser.add_argument("--primitive-examples", action="store_true", help="replay six exact root orders")
    args = parser.parse_args()
    if args.degree is not None:
        try:
            support, width = candidate(args.degree, args.cutoff, args.w)
        except ValueError as e:
            parser.error(str(e))
        bound = 1+(args.degree*(args.degree-1)+width-1)//width
        print(f"Exponents {support}; quotient multiplicity <= {width}; period >= {bound}.")
    if args.audit:
        audit()
    if args.primitive_examples:
        primitive_examples()
    if args.degree is None and not (args.audit or args.primitive_examples):
        parser.error("supply a degree, --audit or --primitive-examples")
