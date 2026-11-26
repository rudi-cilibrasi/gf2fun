"""Check the factor parity obstruction for sparse cube images and its degree-1229 specialization."""

import argparse
import csv
from collections import Counter
from math import gcd, prod
from pathlib import Path

from flint import fmpz, fmpz_mod_poly_ctx
from check_cubed_supports import cube_support, degree_supports
from check_factor_base import DATA


BINARY = fmpz_mod_poly_ctx(2)
X = BINARY.gen()


def polynomial(exponents):
    return sum((X**e for e in exponents), BINARY.zero())


def reciprocal(support):
    n = support[-1]
    return tuple(n-i for i in reversed(support))


def survives_parity(n, support):
    """The two possible sources up to reciprocation in degrees 3 or 5 modulo eight."""
    allowed = set()
    if n % 9 == 2:
        u = (n-2)//3
        allowed.add((0, u, 2*u, 3*u, n))
    if n % 24 == 5:
        allowed.add((0, 1, 3, 4, n))
    return support in allowed or reciprocal(support) in allowed


def parity_audit(limit):
    tails = candidates = 0
    for n in range(19, limit+1, 2):
        if n % 3 == 0:
            continue
        for u in range(1, (n-1)//4+1):
            if (u+n) % 3 or gcd(n, u) != 1:
                continue
            factors = polynomial((0, u, 3*u, 4*u, n)).factor()[1]
            odd = n % 4 == 1 if u == 1 else n % 8 in (1, 7)
            if any(e != 1 for _, e in factors) or len(factors) % 2 != odd:
                raise ArithmeticError(f"quartic-tail factor parity disagrees at {(n, u)}")
            tails += 1
        if n % 8 in (3, 5):
            for s in degree_supports(n):
                if s <= reciprocal(s):
                    if polynomial(s).is_irreducible() and not survives_parity(n, s):
                        raise ArithmeticError(f"the obstruction discarded an irreducible at {s}")
                    candidates += 1
    print(f"Checked {tails} quartic-tail factorizations and {candidates} cube candidates up to reciprocal.")


def check_cube_pair(s):
    n = s[-1]
    f, g = polynomial(s), polynomial(cube_support(s))
    if not f.is_irreducible() or not g.is_irreducible() or g.compose_mod(X**3, f) != 0:
        raise ArithmeticError(f"irreducible cube identity failed at {s}")
    if g.degree() != n:
        raise ArithmeticError("cubing changed the degree")
    return f, g


def degree_27():
    pair = check_cube_pair((0, 7, 10, 17, 27))
    primes = (7, 73, 262657)
    order = 2**27-1
    if prod(primes) != order or not all(fmpz(p).is_prime() for p in primes):
        raise ArithmeticError("incomplete factorization in degree 27")
    for f in pair:
        if X.pow_mod(order, f) != 1 or any(X.pow_mod(order//p, f) == 1 for p in primes):
            raise ArithmeticError("the degree-27 source or cube image is imprimitive")
    if any(polynomial((0, k, 27)).is_irreducible() for k in range(1, 27)):
        raise ArithmeticError("found an irreducible degree-27 trinomial")
    print("Verified a primitive degree-27 pair with taps (7,10,17) and (7,9,10), and excluded all 26 trinomials.")


def degree_1229():
    n = 1229
    supports = degree_supports(n)
    if len(supports) != 478 or any(len(cube_support(s)) != 5 for s in supports):
        raise ArithmeticError("unexpected degree-1229 cube supports")
    reps = {min(s, reciprocal(s)) for s in supports}
    if len(reps) != 239 or any(polynomial(s).is_irreducible() for s in reps):
        raise ArithmeticError("degree-1229 cube exclusion failed")
    survivors = {s for s in supports if survives_parity(n, s)}
    tail = (0, 1, 3, 4, n)
    if survivors != {tail, reciprocal(tail)} or polynomial(tail) % (X**3+X+1) != 0:
        raise ArithmeticError("the two parity survivors or their cubic factor changed")
    source = (0, 11, 33, 66, n)
    if cube_support(source) != (0, 33, 55, 66, 417, 823, n):
        raise ArithmeticError("the claimed minimum-weight cube image changed")
    check_cube_pair(source)
    print("All 478 degree-1229 candidates are reducible. The parity test leaves a reciprocal pair with a cubic factor.")
    print("The minimum cube weight for an irreducible degree-1229 pentanomial is seven, attained at taps (11,33,66).")


def census(path):
    # Use the --list output of census_1229_pentanomials.cpp.
    with (DATA / "degree-1229-pentanomial-census.csv").open(newline="") as stream:
        expected = {int(r["smallest_tap"]): int(r["irreducibles"]) for r in csv.DictReader(stream)}
    counts, histogram = Counter(), Counter()
    previous = (0,)
    with path.open(newline="") as stream:
        for row in csv.DictReader(stream):
            a, b, c = (int(row[k]) for k in ("a", "b", "c"))
            s = (0, a, b, c, 1229)
            if not 0 < a < b < c < 1229 or (a, b, c) <= previous or s >= reciprocal(s):
                raise ArithmeticError(f"invalid reciprocal representative at {s}")
            counts[a] += 1
            histogram[len(cube_support(s))] += 2
            previous = (a, b, c)
    if any(counts[a] != num for a, num in expected.items()) or sum(histogram.values()) != 639166:
        raise ArithmeticError("incomplete irreducible census")
    print("Cube weight and number of irreducible degree-1229 pentanomials in both orientations:")
    for weight, count in sorted(histogram.items()):
        print(weight, count)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, help="independently factor all eligible quartic tails through this degree")
    parser.add_argument("--census", type=Path, help="audit the cube weights of the complete degree-1229 irreducible list")
    args = parser.parse_args()
    degree_27()
    degree_1229()
    if args.through is not None:
        parity_audit(args.through)
    if args.census is not None:
        census(args.census)
