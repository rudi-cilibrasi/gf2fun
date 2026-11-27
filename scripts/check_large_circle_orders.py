"""Verify full and relative multiplicative orders of large sparse binary polynomials."""

import argparse
import json
import subprocess
from math import gcd, isqrt
from pathlib import Path

from flint import fmpz

from make_packed_mersenne import advance, make_stages


DATA = Path(__file__).resolve().parents[1] / "data"


def wagstaff_prime(p, groups):
    """Prove (2^p+1)/3 prime using factored N-1 and a two-factor discriminant."""
    n = fmpz(((1 << p)+1)//3)
    cofactor = n-1
    for base, primes in groups.items():
        a = fmpz(base)
        if pow(a, n-1, n) != 1:
            raise ArithmeticError(f"Fermat witness failed at p={p}, base {a}")
        for prime in primes:
            if not fmpz(prime).is_prime() or cofactor % prime:
                raise ArithmeticError(f"invalid factor of N-1 at p={p}: {prime}")
            if gcd(pow(a, (n-1)//prime, n)-1, n) != 1:
                raise ArithmeticError(f"order witness failed at p={p}, prime {prime}")
            while cofactor % prime == 0:
                cofactor //= prime

    # Each prime divisor of n is 1 mod F. If n < F^3 were composite,
    # it would equal (aF+1)(bF+1), with a+b < F. Dividing (n-1)/F
    # by F would give quotient ab and remainder a+b.
    f = (n-1)//cofactor
    if f**3 <= n:
        raise ArithmeticError(f"insufficient factored portion of N-1 at p={p}")
    product, total = divmod(cofactor, f)
    discriminant = total**2 - 4*product
    if discriminant >= 0 and isqrt(discriminant)**2 == discriminant:
        raise ArithmeticError(f"the two-factor test was inconclusive at p={p}")
    return int(n)


def mersenne_prime(n):
    if n <= 2 or not fmpz(n).is_prime():
        raise ArithmeticError(f"invalid Lucas–Lehmer exponent {n}")
    m = fmpz((1 << n)-1)
    residue = fmpz(4)
    for _ in range(n-2):
        residue = (residue*residue-2) % m
    if residue != 0:
        raise ArithmeticError(f"Lucas–Lehmer test failed in degree {n}")


def check_published_86243():
    """Replay Table 2 of Kumada et al., Keio report KSTS/RR-98/009 (1998)."""
    n = 86243
    mersenne_prime(n)
    stages = make_stages(n)
    for taps in ((11754, 50942, 62833), (19434, 41667, 64043)):
        # n iterations of v -> X*v^2 starting at 1 give X^(2^n-1).
        if advance(1, n, [n, *taps, 0], stages, n) != 1:
            raise ArithmeticError(f"full power failed for degree {n} and taps {taps}")
        print(f"Degree {n}, taps {taps}: primitive, with full order 2^{n}-1.", flush=True)


def field_check(gp, exponents, powers):
    """Check irreducibility and each requested nonidentity power independently in PARI/GP."""
    n = exponents[-1]
    if len(exponents) != 5 or exponents[0] != 0 or exponents != sorted(set(exponents)):
        raise ValueError(f"expected five distinct sorted exponents: {exponents}")
    f = "+".join(f"x^{e}" for e in exponents)
    # GP expressions below use only integers from the input and fixed arithmetic formulas.
    tests = "\n".join(f'if(t^({power})==1,error("order test {i}"));' for i, power in enumerate(powers))
    program = f'''run()={{
      my(f=Mod(1,2)*({f}),t);
      if(!polisirreducible(f),error("reducible polynomial")); t=ffgen(f,'z);
      {tests}
    }};
    iferr(run(),err,print(err);quit(1));
    print("verified");
    '''
    result = subprocess.run([gp, "-fq", "-s", "256M"], input=program, text=True, capture_output=True)
    if result.returncode or result.stdout.strip() != "verified" or result.stderr.strip():
        raise ArithmeticError(f"degree {n} field check failed: {result.stdout} {result.stderr}")


def check_quadratic(p, row, gp):
    if not fmpz(p).is_prime() or row["exponents"][-1] != 2*p:
        raise ArithmeticError(f"invalid quadratic degree for {p}")
    w = wagstaff_prime(p, row["wagstaff_witnesses"])
    q = 1 << p
    cofactor = q-1
    powers = [f"3*(2^{p}-1)", f"(2^{2*p}-1)/3"]
    for prime in row["subfield_primes"]:
        if not fmpz(prime).is_prime() or cofactor % prime:
            raise ArithmeticError(f"invalid subfield factor {prime} in degree {2*p}")
        while cofactor % prime == 0:
            cofactor //= prime
        powers.append(f"(2^{2*p}-1)/{prime}")
    known = (q-1)//cofactor
    powers.append(f"(2^{p}+1)*{known}")
    field_check(gp, row["exponents"], powers)
    if 3*w != q+1 or gcd(known, cofactor) != 1:
        raise ArithmeticError(f"relative-order factors disagree in degree {2*p}")
    # Each prime divisor of the unresolved cofactor is 1 mod 2p.
    bound = (q+1)*known*(2*p+1)
    print(f"Degree {2*p}: full relative order 2^{p}+1; full-group index divides "
          f"a {len(str(cofactor))}-digit cofactor; root order has at least {len(str(bound))} digits.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    parser.add_argument("--degree", type=int, help="check one archived degree")
    args = parser.parse_args()
    quadratic = json.loads((DATA / "large-quadratic-circle-orders.json").read_text())
    checked = 0
    for p, row in quadratic.items():
        if args.degree is None or args.degree == 2*int(p):
            check_quadratic(int(p), row, args.gp)
            checked += 1
    for exponents in json.loads((DATA / "large-mersenne-complementary-taps.json").read_text()):
        n = exponents[-1]
        if args.degree is None or args.degree == n:
            mersenne_prime(n)
            field_check(args.gp, exponents, [])
            print(f"Degree {n}: primitive, with full order 2^{n}-1.", flush=True)
            checked += 1
    if args.degree is None or args.degree == 86243:
        check_published_86243()
        checked += 2
    if not checked:
        parser.error("the requested degree has no entry")
