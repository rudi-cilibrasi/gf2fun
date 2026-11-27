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
from check_twisted_cubic import eligible


GP_FILE = Path(__file__).with_name("twisted_ray_class.gp").resolve()


def ray_quotient(gp, p, d):
    command = f"print(twisted_ray_quotient({p},{d}))\n"
    run = subprocess.run([gp, "-fq", "-s", "128M", str(GP_FILE)], input=command,
                         text=True, capture_output=True, check=True)
    if run.stderr or not run.stdout.strip():
        raise ValueError(f"ray computation failed at p={p}, d={d}: {run.stderr}")
    ordinary, ray, quotient = ast.literal_eval(run.stdout.strip())
    if min(ordinary, ray, quotient) < 1 or ray % ordinary or ray % quotient:
        raise ValueError(f"inconsistent class orders at p={p}, d={d}")
    return ordinary, ray, quotient


def compare(pair, gp):
    p, d = pair
    ordinary, ray, quotient = ray_quotient(gp, p, d)
    n = p - 1
    j = next(i for i in range(n) if pow(2, i, p) == 3)
    correction = gcd((1 << (n // 2)) - 1, (1 << j) - 3)
    modulus = cyclotomic_form(p)
    group = (1 << n) - 1
    failed = []
    primes = [int(l) for l, _ in fmpz((1 << d) - 1).factor()]
    for l in primes:
        binary_failure = X.pow_mod(group // l, modulus) == 1
        predicted = quotient % l == 0 or correction % l == 0
        if binary_failure != predicted:
            raise ValueError(f"ray and binary tests disagree at p={p}, d={d}, prime={l}")
        if predicted:
            failed.append(l)
    return p, d, ordinary, ray, quotient, primes, failed


def sample():
    for p in range(5, 2054, 8):
        if eligible(p):
            degrees = {2, 3, 4}
            if p <= 149:
                degrees.update((5, 6))
            if p == 13:
                degrees.add(p - 1)
            yield from ((p, d) for d in sorted(degrees) if (p - 1) % d == 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--case", type=int, nargs=2, metavar=("P", "DEGREE"))
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("jobs must be positive")
    if args.case:
        p, d = args.case
        if not eligible(p) or d < 2 or (p - 1) % d:
            parser.error("use a prime p congruent to five mod eight with two primitive, and d > 1 dividing p-1")
        rows = [(p, d)]
    else:
        rows = list(sample())
    comparisons = 0
    with ThreadPoolExecutor(args.jobs) as pool:
        for p, d, ordinary, ray, quotient, primes, failed in pool.map(partial(compare, gp=args.gp), rows):
            comparisons += len(primes)
            print(f"p={p} d={d} class={ordinary} ray={ray} quotient={quotient} failing={failed}", flush=True)
    print(f"Verified {len(rows)} ray quotients and {comparisons} binary prime-index tests.")


if __name__ == "__main__":
    main()
