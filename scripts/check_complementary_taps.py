"""Check the discriminant, candidate count and even-spacing census for complementary taps."""

import argparse
import csv
import json
import subprocess
import sys
from collections import Counter
from functools import cache
from math import gcd, lcm
from pathlib import Path

from flint import fmpz, fmpz_poly, nmod_poly


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


def check_spacing_bound():
    spacings = Counter()
    for start, end, step in ((5, 1228, 1), (1230, 2292, 2)):
        with (DATA / f"symmetric-witnesses-{start}-{end}.csv").open(newline="") as source:
            for n, row in zip(range(start, end+1, step), csv.DictReader(source), strict=True):
                degree, b, a = (int(row[key]) for key in ("degree", "b", "a"))
                if degree != n or not 1 <= b <= 13 or (n == 2040 and (b, a) != (13, 8)):
                    raise ArithmeticError(f"spacing bound failed in degree {n}")
                spacings[b] += 1
    if spacings[1] != 1113 or sum(spacings.values()) != 1756:
        raise ArithmeticError("unexpected spacing counts")


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
    if total != 12336 or failures != {3: 29, 5: 12, 7: 9, 11: 1, 13: 3, 17: 1, 43: 1, 137: 1}:
        raise ArithmeticError(f"unexpected census: {total} candidates, {failures}")
    print(f"In the 18 exceptions, {total} reciprocal pairs give 57 irreducibles. "
          f"Their proper-order divisors and counts are {dict(sorted(failures.items()))}.")


def check_spacing_2040(gp):
    n = 2040
    pairs = [(b, a) for b in range(1, 13) for a in range(1, n//2+1)
             if a != b and gcd(gcd(b, n), a) == 1]
    failures = order_obstructions(n, pairs, gp)
    if len(pairs) != 7851 or failures != {3: 5, 5: 2, 7: 2, 13: 2}:
        raise ArithmeticError(f"unexpected degree-2040 order obstructions: {failures}")
    print(f"In degree 2040, {len(pairs)} pairs with spacings 1 through 12 and coprime "
          f"exponents give {sum(failures.values())} irreducibles of proper order. "
          f"The divisors and counts are {dict(sorted(failures.items()))}.")


@cache
def no_field_root(order, half_degree, tap):
    """GCD with Y^order + 1, with the binary polynomial coefficients packed in an integer."""
    polynomial = 0
    for exponent in (0, 2, 2*half_degree-2, 2*half_degree, tap):
        polynomial ^= 1 << (exponent % order)
    modulus = (1 << order) | 1
    while polynomial:
        shift = modulus.bit_length() - polynomial.bit_length()
        if shift < 0:
            modulus, polynomial = polynomial, modulus
        else:
            modulus ^= polynomial << shift
    return modulus == 1


@cache
def field_orbits(d, tap_count):
    """Logarithms of 1+Y^i and one exponent per nonidentity Frobenius orbit."""
    size = 1 << d
    order = size-1
    for low in range(1, size, 2):
        modulus = size | low
        logs = [-1]*size
        powers = []
        value = 1
        while logs[value] == -1:
            logs[value] = len(powers)
            powers.append(value)
            value <<= 1
            if value >= size:
                value ^= modulus
        if len(powers) == order:
            break
    else:
        raise ArithmeticError(f"no primitive field modulus in degree {d}")
    log_one_plus = [logs[value ^ 1] for value in powers]
    seen = bytearray(order)
    orbits = []
    patterns = {}
    for u in range(1, order):
        if seen[u]:
            continue
        v = u
        while not seen[v]:
            seen[v] = 1
            v = 2*v % order
        divisor = gcd(u, order)
        step = order//divisor
        if step not in patterns:
            patterns[step] = sum(1 << k for k in range(0, tap_count, step))
        orbits.append((u, divisor, step, pow(u//divisor, -1, step),
                       log_one_plus[2*u % order], patterns[step]))
    return log_one_plus, orbits


@cache
def excluded_taps(d, g, tap_count):
    order = 2**d-1
    exponent = 2*g-2
    if exponent % order == 0:
        return 0
    log_one_plus, orbits = field_orbits(d, tap_count)
    excluded = 0
    for u, divisor, step, inverse, first_log, pattern in orbits:
        second_log = log_one_plus[exponent*u % order]
        if second_log < 0:
            continue
        # At Y = generator^u the root equation is u*k = first_log + second_log (mod order).
        total = first_log + second_log
        if total % divisor == 0:
            k = (total//divisor)*inverse % step
            if k < tap_count:
                excluded |= pattern << k
    return excluded


def check_local_cutoff(bound):
    period = lcm(*(2**d-1 for d in range(1, bound+1)))
    divisors = [1]
    for prime, exponent in fmpz(period).factor():
        divisors = [d*int(prime)**j for d in divisors for j in range(exponent+1)]
    # Each field of degree <= bound embeds in one of these fields.
    fields = [(d, 2**d-1) for d in range(bound//2+1, bound+1)]
    tap_count = 110
    largest = -1
    for g in sorted(divisors):
        choices = (1 << tap_count)-1
        for d, order in fields:
            choices &= ~excluded_taps(d, g % order, tap_count)
        if not choices:
            raise ArithmeticError(f"no local certificate found at divisor {g} of period {period}")
        least = (choices & -choices).bit_length()-1
        if least > largest:
            largest, hardest = least, g
    # Independently repeat all smaller tap tests and the successful one in the hardest class.
    for k in range(largest+1):
        passed = all(no_field_root(h, hardest % h, k % h) for _, h in fields)
        if passed != (k == largest):
            raise ArithmeticError(f"root enumeration and polynomial gcd disagree at {(hardest, k)}")
    print(f"Degree cutoff {bound}, period {period}: covered all {len(divisors)} "
          f"gcd classes. The largest of the least tap residues is {largest}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", action="store_true", help="check the even-spacing and degree-2040 censuses with PARI/GP")
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    parser.add_argument("--local-cutoff", type=int, choices=range(1, 17), metavar="B",
                        help="certify the root-free residue choices in every gcd class, for 1 <= B <= 16")
    parser.add_argument("--candidates", type=int, metavar="N",
                        help="write the even-spacing reciprocal representatives in degree N as CSV (8 divides N)")
    args = parser.parse_args()
    if args.candidates is not None:
        n = args.candidates
        if n < 8 or n % 8 or args.census or args.local_cutoff:
            parser.error("--candidates takes a positive multiple of eight and runs by itself")
        writer = csv.writer(sys.stdout, lineterminator="\n")
        writer.writerow(("degree", "b", "a"))
        writer.writerows((n, b, a) for b, a in candidates(n))
        sys.exit(0)
    check_formula()
    check_spacing_bound()
    if args.census:
        check_even_spacing_census(args.gp)
        check_spacing_2040(args.gp)
    if args.local_cutoff:
        check_local_cutoff(args.local_cutoff)
