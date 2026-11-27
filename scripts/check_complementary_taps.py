"""Check the discriminant, candidate count and even-spacing census for complementary taps."""

import argparse
import csv
import json
import subprocess
from collections import Counter
from math import gcd
from pathlib import Path

from flint import fmpz_poly, nmod_poly


DATA = Path(__file__).resolve().parents[1] / "data"
ODD_SPACING_REQUIRED = (
    24, 192, 288, 312, 360, 408, 552, 576, 600, 696, 952, 1056, 1080,
    1464, 1560, 1584, 1896, 2064,
)


def discriminant_mod_eight(n, b, a):
    correction = 0
    for d in (b, n-b):
        if d % 4 == 2:
            t = d // 2
            correction += (a % t == 0) + ((a-(n-d)) % t == 0)
    return (-1)**(n//2) * (1-n*pow(a, -1, 8)) * (1+4*correction) % 8


def candidates(n):
    """One representative of each pair passing factor parity and exponent coprimality, for 8 | n."""
    m = n // 2
    for t in range(1, m//2, 2):
        s = m-t
        if gcd(t, s) != 1:
            continue
        taps = {min(a, n-a) for u in (t, s) for a in range(u, n, 2*u)}
        for a in sorted(taps):
            if discriminant_mod_eight(n, 2*t, a) == 5:
                yield 2*t, a


def check_formula():
    x = fmpz_poly([0, 1])
    checked = 0
    for n in range(6, 65, 2):
        for b in range(2, n//2, 2):
            base = (1+x**b) * (1+x**(n-b))
            for a in range(1, n, 2):
                f = base+x**a
                disc = discriminant_mod_eight(n, b, a)
                factors = nmod_poly(list(f), 2).factor()[1]
                if (f.discriminant() % 8 != disc or any(e != 1 for _, e in factors)
                        or len(factors) % 2 != (disc == 5)):
                    raise ArithmeticError(f"discriminant or factorization failed at {(n, b, a)}")
                checked += 1
    for n in range(8, 257, 8):
        brute = {(b, a) for b in range(2, n//2, 2) for a in range(1, n//2, 2)
                 if gcd(gcd(b, n), a) == 1 and discriminant_mod_eight(n, b, a) == 5}
        if set(candidates(n)) != brute:
            raise ArithmeticError(f"reciprocal representatives disagree in degree {n}")
    for n in range(24, 2293, 8):
        m = n//2
        count = 1 + sum((n+u-1)//(2*u) for u in range(3, m-1, 2) if gcd(u, m) == 1)
        if sum(1 for _ in candidates(n)) != count:
            raise ArithmeticError(f"exact count failed in degree {n}")
    print(f"Checked {checked} integer discriminants and binary factorizations, "
          "and the exact count for every multiple of eight from 24 through 2288.")


def order_obstructions(n, pairs, gp):
    """PARI finds every irreducible in the list, then FLINT proves each has proper order."""
    commands = [f"if(polisirreducible(Mod(1,2)*((1+x^{b})*(1+x^{n-b})+x^{a})),print([{b},{a}]));"
                for b, a in pairs]
    commands.append('print("done");')
    run = subprocess.run([gp, "-fq", "-s", "256M"], input="\n".join(commands)+"\n",
                         capture_output=True, text=True, check=True)
    lines = run.stdout.splitlines()
    if run.stderr or not lines or lines[-1] != "done":
        raise ArithmeticError(f"PARI failed in degree {n}: {run.stderr}")
    x = nmod_poly([0, 1], 2)
    order = 2**n-1
    failures = Counter()
    for line in lines[:-1]:
        b, a = json.loads(line)
        f = (1+x**b) * (1+x**(n-b)) + x**a
        divisor = next((d for d in range(3, 1000, 2) if order % d == 0
                        and x.pow_mod(order//d, f) == 1), None)
        if divisor is None:
            raise ArithmeticError(f"missing order obstruction at {(n, b, a)}")
        failures[divisor] += 1
    return failures


def check_even_spacing_census(gp):
    rows = {}
    with (DATA / "symmetric-witnesses-multiples-of-eight-through-2288.csv").open(newline="") as source:
        for row in csv.DictReader(source):
            n, b, a = (int(row[key]) for key in ("degree", "b", "a"))
            if n in rows:
                raise ArithmeticError(f"repeated witness in degree {n}")
            rows[n] = b, min(a, n-a)
    if (sorted(rows) != list(range(8, 2293, 8))
            or tuple(sorted(n for n, (b, _) in rows.items() if b % 2)) != ODD_SPACING_REQUIRED):
        raise ArithmeticError("the witness tables disagree with the claimed degree sets")
    for n, (b, a) in rows.items():
        if b % 2 == 0 and (b, a) not in candidates(n):
            raise ArithmeticError(f"the certified degree-{n} witness failed the candidate test")

    total = 0
    failures = Counter()
    for n in ODD_SPACING_REQUIRED:
        pairs = list(candidates(n))
        total += len(pairs)
        failures.update(order_obstructions(n, pairs, gp))
    if total != 12336 or sum(failures.values()) != 57:
        raise ArithmeticError(f"unexpected census: {total} candidates, {failures}")
    print(f"In the 18 exceptions, {total} reciprocal pairs give 57 irreducibles. "
          f"Their proper-order divisors and counts are {dict(sorted(failures.items()))}.")


def check_spacing_2040(gp):
    n = 2040
    pairs = [(b, a) for b in range(1, 13) for a in range(1, n//2+1)
             if a != b and gcd(gcd(b, n), a) == 1]
    failures = order_obstructions(n, pairs, gp)
    print(f"In degree 2040, {len(pairs)} pairs with spacings 1 through 12 and coprime "
          f"exponents give {sum(failures.values())} irreducibles of proper order. "
          f"The divisors and counts are {dict(sorted(failures.items()))}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", action="store_true", help="check the even-spacing and degree-2040 censuses with PARI/GP")
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    args = parser.parse_args()
    check_formula()
    if args.census:
        check_even_spacing_census(args.gp)
        check_spacing_2040(args.gp)
