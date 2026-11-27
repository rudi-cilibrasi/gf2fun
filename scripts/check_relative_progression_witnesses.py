"""Verify the certified part of two progression root orders with composite subfield cofactors."""

import argparse
import json
import sys
from math import gcd, prod
from pathlib import Path

from flint import fmpz

from check_factor_base import irreducible, modulus, polynomial
from check_primo_certificate import check_primo
from check_product_range import prime_index_powers


DATA = Path(__file__).resolve().parents[1] / "data"
TRIAL_LIMIT = 10**10


def verify_dilations():
    x = polynomial(2)
    for n, tap, order in ((63, 49, 3577), (147, 35, 14680057)):
        f = modulus(n, (7, 14, tap))
        if not irreducible(f) or x.pow_mod(order, f) != 1:
            raise ArithmeticError(f"invalid dilated polynomial at {n}")
        if any(x.pow_mod(order//int(p), f) == 1 for p, _ in fmpz(order).factor()):
            raise ArithmeticError(f"incorrect order for the dilation at {n}")
        a, b = (1 << (n//3))-1, (1 << (n//7))-1
        if ((a // gcd(a, b)) * b % order == 0) != (pow(2, n//21, 7) == 1):
            raise ArithmeticError(f"incorrect subfield prediction at {n}")


def verify(n, row, gp):
    p, q = sorted(int(p) for p, _ in fmpz(n).factor())
    a, b = (1 << (n//p))-1, (1 << (n//q))-1
    order = (1 << n)-1
    prime = order // ((a // gcd(a, b)) * b)
    check_primo(DATA / f"degree-{n}-primality.cert.gz", prime, gp)
    known_primes = [*row["known_lower_primes"], prime]
    if not all(fmpz(v).is_prime() for v in row["known_lower_primes"]):
        raise ArithmeticError(f"composite known lower factor at {n}")
    known = prod(known_primes)
    cofactor = row["remaining_cofactor"]
    if cofactor <= 1 or cofactor * known != order or gcd(cofactor, known) != 1:
        raise ArithmeticError(f"incorrect cofactor at {n}")

    d, = [d for d in (n//p, n//q) if ((1 << d)-1) % cofactor == 0]
    if any(gcd(cofactor, (1 << (d//int(v)))-1) != 1 for v, _ in fmpz(d).factor()):
        raise ArithmeticError(f"a remaining prime may have binary degree below {d}")
    if any(cofactor % k == 0 for k in range(2*d+1, TRIAL_LIMIT+1, 2*d)):
        raise ArithmeticError(f"small divisor of the cofactor at {n}")

    taps = row["taps"]
    if taps[:2] != [1, 2] or len(taps) != 3 or not 2 < taps[2] < n:
        raise ValueError(f"invalid progression taps at {n}")
    f = modulus(n, taps)
    x = polynomial(2)
    if x.pow_mod(order, f) != 1 or any((x.pow_mod(1 << d, f)+x).gcd(f) != 1 for d in (n//p, n//q)):
        raise ArithmeticError(f"irreducibility test failed at {n}")
    if any(z == 1 for _, z in prime_index_powers(x, order, sorted(set(known_primes)), f)):
        raise ArithmeticError(f"missing known factor in degree {n}")
    if x.pow_mod(known, f) == 1:
        raise ArithmeticError(f"trivial cofactor component at {n}")
    print(f"Degree {n}: {len(str(known))}-digit divisor of the root order, "
          f"remaining component exceeds {TRIAL_LIMIT}, every cofactor prime has binary degree {d}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for PRIMO verification")
    parser.add_argument("--degree", type=int, choices=(6925, 12231))
    args = parser.parse_args()
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    verify_dilations()
    rows = json.loads((DATA / "relative-progression-witnesses.json").read_text())
    for n in [args.degree] if args.degree else map(int, rows):
        verify(n, rows[str(n)], args.gp)


if __name__ == "__main__":
    main()
