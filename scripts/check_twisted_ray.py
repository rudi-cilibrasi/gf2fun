"""Compare certified number-field ray quotients with binary root-order tests for D_p."""

import argparse
import ast
import subprocess
from concurrent.futures import ThreadPoolExecutor
from functools import partial
from math import gcd
from pathlib import Path

from flint import fmpz

from check_translation_lift_orders import X, cyclotomic_form


GP_FILE = Path(__file__).with_name("twisted_ray_class.gp").resolve()


def eligible(p):
    if p < 5 or p % 8 not in (5, 7) or not fmpz(p).is_prime():
        return False
    return all(l.is_prime() and pow(-2, (p - 1) // int(l), p) != 1 for l, _ in fmpz(p - 1).factor())


def run_gp(gp, expression):
    run = subprocess.run([gp, "-fq", "-s", "128M", str(GP_FILE)], input=f"print({expression})\n",
                         text=True, capture_output=True, check=True)
    if run.stderr or not run.stdout.strip():
        raise ValueError(f"PARI failed on {expression}: {run.stderr}")
    return run.stdout.strip()


def ray_quotient(gp, p, d):
    ordinary, ray, quotient = ast.literal_eval(run_gp(gp, f"twisted_ray_quotient({p},{d})"))
    if min(ordinary, ray, quotient) < 1 or ray % ordinary or ray % quotient:
        raise ValueError(f"inconsistent class orders at p={p}, d={d}")
    return ordinary, ray, quotient


def compare(pair, gp):
    p, d = pair
    ordinary, ray, quotient = ray_quotient(gp, p, d)
    n = p - 1
    j = next(i for i in range(n) if pow(2, i, p) in (3, p - 3))
    correction = gcd((1 << (n // 2)) - 1, (1 << j) - 3)
    modulus = cyclotomic_form(p)
    group = (1 << n) - 1
    half_group = (1 << (n // 2)) - 1
    inverse_period = (X**2 + X + 1) % modulus
    failed = []
    primes = [int(l) for l, _ in fmpz((1 << d) - 1).factor()]
    for l in primes:
        binary_failure = X.pow_mod(group // l, modulus) == 1
        predicted = quotient % l == 0 or correction % l == 0
        if binary_failure != predicted:
            raise ValueError(f"ray and binary tests disagree at p={p}, d={d}, prime={l}")
        if half_group % l == 0:
            period_failure = inverse_period.pow_mod(half_group // l, modulus) == 1
            if period_failure != (quotient % l == 0):
                raise ValueError(f"Gauss period and ray tests disagree at p={p}, d={d}, prime={l}")
        if predicted:
            failed.append(l)
    return p, d, ordinary, ray, quotient, primes, failed


def sample():
    for p in range(5, 2054, 2):
        if eligible(p):
            degrees = {2, 3, 4}
            if p <= 149:
                degrees.update((5, 6))
            if p in (7, 13):
                degrees.add(p - 1)
            yield from ((p, d) for d in sorted(degrees) if (p - 1) % d == 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    parser.add_argument("--jobs", type=int, default=1)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--case", type=int, nargs=2, metavar=("P", "DEGREE"))
    modes.add_argument("--fields", type=int, metavar="K",
                       help="certify and print the degree 2, 3 and 4 fields for C_K")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("jobs must be positive")
    if args.fields is not None:
        if args.fields < 3 or args.fields % 2 == 0:
            parser.error("C_K requires an odd K of at least three")
        p = (1 << args.fields) + 5
        for d in (2, 3, 4):
            polynomial = run_gp(args.gp, f"twisted_ray_field({p},{d})")
            print(f"C_{args.fields} E_{d}: {polynomial}")
        return
    if args.case:
        p, d = args.case
        if not eligible(p) or d < 2 or (p - 1) % d:
            parser.error("use a prime p with -2 primitive modulo p, and d > 1 dividing p-1")
        rows = [(p, d)]
    else:
        rows = list(sample())
    comparisons = 0
    period_comparisons = 0
    with ThreadPoolExecutor(args.jobs) as pool:
        for p, d, ordinary, ray, quotient, primes, failed in pool.map(partial(compare, gp=args.gp), rows):
            comparisons += len(primes)
            period_comparisons += sum(pow(2, (p - 1) // 2, l) == 1 for l in primes)
            print(f"p={p} d={d} class={ordinary} ray={ray} quotient={quotient} failing={failed}", flush=True)
    print(f"Verified {len(rows)} ray quotients, {comparisons} twisted root tests, "
          f"and {period_comparisons} Gauss period tests.")


if __name__ == "__main__":
    main()
