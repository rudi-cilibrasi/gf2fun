"""Classify two-odd-tap product pentanomials in odd degree by binary polynomial arithmetic."""

import argparse
import csv
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from functools import partial
from pathlib import Path

from flint import fmpz_poly, nmod_poly


X = nmod_poly([0, 1], 2)
Y = fmpz_poly([0, 1])
DATA = Path(__file__).resolve().parents[1] / "data"


def factor_parity(n, u, v):
    """Compute the parity using one cyclic inverse, with None for a repeated factor."""
    h, d, a = (u+v)//2, (v-u)//2, (n-u)//2
    cyclic = 1 + X**h
    trinomial = 1 + X**(d % h) + X**(a % h)
    common, inverse, _ = trinomial.xgcd(cyclic)
    if common != 1:
        return None

    bit = 0
    # The constant coefficient of S(Y) (Y P'(Y)) P(Y) H(Y)^2 modulo Y^(2h)+1.
    for w in (u, v):
        if (n+w) % 4 == 0:
            for e in (d, a):
                if e % 2:
                    for k in (0, d, a):
                        exponent = w+e+k
                        if exponent % 2 == 0:
                            bit ^= int(inverse[(-exponent//2) % h])
    if h % 2:
        bit ^= int(inverse[(-d//2) % h])
        if a % 2:
            bit ^= 1 ^ int(inverse[(-a) % h])
    return int(n % 8 in (1, 7)) ^ bit


def audit_tap(u, n, factor, integer, joint):
    counts = Counter()
    irreducibles = []
    for v in range(u+2, n-u, 2):
        parity = factor_parity(n, u, v)
        counts["repeated" if parity is None else "odd" if parity else "even"] += 1
        if factor or (joint and parity):
            f = X**n + (1+X**u)*(1+X**v)
        if factor:
            factors = f.factor()[1]
            actual = None if any(e != 1 for _, e in factors) else len(factors) % 2
            if actual != parity:
                raise ArithmeticError(f"factorization disagrees at {(n, u, v)}")
            if len(factors) == 1 and factors[0][1] == 1:
                irreducibles.append((u, v))
        if integer:
            lift = Y**n + (1+Y**u)*(1+Y**v)
            disc = int(lift.discriminant()) % 8
            if (disc % 2 == 0) != (parity is None) or (parity is not None and disc != (1 if parity else 5)):
                raise ArithmeticError(f"integer discriminant disagrees at {(n, u, v)}")
        if joint and parity and f.gcd(f.reverse()) == 1:
            for degree in range(1, 6):
                if f.gcd(X**(2**degree) + X) != 1:
                    break
                counts[degree] += 1
    return counts, irreducibles


def census(n, pool, factor, integer, joint):
    work = partial(audit_tap, n=n, factor=factor, integer=integer, joint=joint)
    taps = range(1, n//2+1, 2)
    counts = Counter()
    irreducibles = set()
    for local, hits in (pool.map(work, taps) if pool else map(work, taps)):
        counts.update(local)
        irreducibles.update(hits)
    return counts, irreducibles


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--through", type=int, default=80, help="factor every odd-degree support through this limit")
    mode.add_argument("--degree", type=int, help="classify all two-odd-tap supports in one odd degree")
    parser.add_argument("--factor", action="store_true", help="independently factor every support in the selected degree")
    parser.add_argument("--joint", action="store_true", help="count survivors also avoiding inverse pairs and small factors")
    parser.add_argument("--jobs", type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1 or args.through < 7 or (args.degree is not None and (args.degree < 7 or args.degree % 2 == 0)):
        parser.error("expected positive jobs and degrees of at least seven, with --degree odd")
    if (args.factor or args.joint) and args.degree is None:
        parser.error("--factor and --joint require --degree")
    with ProcessPoolExecutor(args.jobs) as pool:
        workers = pool if args.jobs > 1 else None
        if args.degree is None:
            total = sum(sum(census(n, workers, True, n <= 48, False)[0].values())
                        for n in range(7, args.through+1, 2))
            print(f"Verified {total:,} two-odd-tap supports through degree {args.through}.")
        else:
            n = args.degree
            counts, irreducibles = census(n, workers, args.factor, False, args.joint)
            print(f'Degree {n}: {counts["repeated"]:,} repeated, {counts["even"]:,} squarefree even, '
                  f'{counts["odd"]:,} squarefree odd.')
            if args.factor:
                with (DATA / "open-product-irreducibles.csv").open(newline="") as stream:
                    rows = [r for r in csv.DictReader(stream) if int(r["degree"]) == n]
                if rows:
                    published = {(int(r["u"]), int(r["v"])) for r in rows if int(r["u"])*int(r["v"]) % 2}
                    if irreducibles != published:
                        raise ArithmeticError("direct factorization and published support list disagree")
                print(f"Direct factorizations contain {len(irreducibles):,} irreducibles.")
            if args.joint:
                for k in range(1, 6):
                    print(f"Cutoff {k} and no inverse pair: {counts[k]:,} survivors.")
