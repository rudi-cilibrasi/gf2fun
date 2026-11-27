"""Check twisted cyclotomic root orders using ray class numbers and a half-field power."""

import argparse
import ast
import subprocess
from math import gcd

from flint import fmpz

from check_translation_lift_orders import X, cyclotomic_form
from check_twisted_ray import GP_FILE, run_gp


def eligible(p):
    if p % 8 != 5 or not fmpz(p).is_prime():
        return False
    return all(pow(2, (p - 1) // int(l), p) != 1 for l, _ in fmpz(p - 1).factor())


def check(gp):
    primes = [p for p in range(5, 2054, 8) if eligible(p)]
    # At conductor two the residue units of Z/2 are trivial, so the ordinary
    # ray class number is the Picard number of the order of discriminant 4p.
    function = (
        'raytwo(p)={my(b=bnfinit(y^2-y+(1-p)/4,1));'
        'if(!bnfcertify(b),error("uncertified quadratic class group"));'
        'bnrinit(b,2).no};'
    )
    commands = [function, *(f'print([raytwo({p}),twisted_cubic_reflection({p})]);' for p in primes)]
    run = subprocess.run([gp, "-qf", str(GP_FILE)], input="\n".join(commands) + "\n",
                         text=True, capture_output=True, check=True)
    values = [ast.literal_eval(line) for line in run.stdout.splitlines()]
    if run.stderr or len(values) != len(primes):
        raise ValueError(f"incomplete certified ray class numbers: {run.stderr}")
    cubes = []
    forced = {}
    for p, (h, (imaginary_h, t, form)) in zip(primes, values):
        f = cyclotomic_form(p)
        group_order = (1 << (p - 1)) - 1
        root_is_cube = X.pow_mod(group_order // 3, f) == 1
        reflected = (imaginary_h // t) % 3 == 0 or form[0] == 1
        if root_is_cube != (h % 3 == 0) or root_is_cube != reflected:
            raise ValueError(f"cubic character mismatch for p={p}, h(4p)={h}")
        if root_is_cube:
            cubes.append(p)
        # With b = x(x+1), the half-field period t satisfies 1/t = b+1.
        # Test b² = t^(2^j-3) directly in the field defined by D_p.
        j = next(i for i in range(p - 1) if pow(2, i, p) == 3)
        exponent = (1 << j) - 3
        b = (X**2 + X) % f
        if (b**2 * (b + 1).pow_mod(exponent, f)) % f != 1:
            raise ValueError(f"half-field identity failed for p={p}")
        common = gcd(exponent, (1 << ((p - 1) // 2)) - 1)
        if common > 1:
            if X.pow_mod(group_order // common, f) != 1:
                raise ValueError(f"missing forced index divisor for p={p}")
            forced[p] = common
    if forced != {461: 47, 1621: 11, 1741: 11}:
        raise ValueError(f"unexpected forced divisors {forced}")
    print(f"Verified {len(primes)} real ray class numbers, imaginary form tests and binary cubic characters through p=2053.")
    print(f"The {len(cubes)} cube cases have p in {cubes}.")
    print(f"The half-field identity forces these index divisors: {forced}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    parser.add_argument("--reflection-survey", type=int, metavar="LIMIT",
                        help="also compare real and imaginary class tests for all primes p = 5 mod 8 through LIMIT")
    args = parser.parse_args()
    check(args.gp)
    if args.reflection_survey is not None:
        if args.reflection_survey < 5:
            parser.error("the survey limit must be at least five")
        counts = ast.literal_eval(run_gp(args.gp, f"twisted_cubic_reflection_survey({args.reflection_survey})"))
        print(f"Through {args.reflection_survey}, among {sum(counts)} primes: {counts[0]} neither test, "
              f"{counts[1]} class quotient only, {counts[2]} lifted form only, {counts[3]} both.")
