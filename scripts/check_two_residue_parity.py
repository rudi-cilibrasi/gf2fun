"""Check discriminants and factor counts for binary polynomials on two residues mod 4."""

import argparse
from itertools import product

from flint import fmpz_mod_poly_ctx, fmpz_poly


def check(through):
    binary = fmpz_mod_poly_ctx(2)
    checked = squarefree = 0
    for n in range(1, through + 1):
        for s in (1, 3):
            if n % 4 not in (0, s):
                continue
            interior = [i for i in range(1, n) if i % 4 in (0, s)]
            for taps in product((0, 1), repeat=len(interior)):
                coeff = [1] + [0] * (n - 1) + [1]
                for i, bit in zip(interior, taps):
                    coeff[i] = bit
                u, v = binary(coeff[::4]), binary(coeff[s::4])
                if s == 3 and v.is_zero():
                    continue  # A fourth power was already checked with s = 1.
                f = binary(coeff)
                checked += 1
                separable = f.is_squarefree()
                if separable != (u.gcd(v) == 1):
                    raise ArithmeticError(f"squarefreeness mismatch for {f}")
                if not separable:
                    continue
                squarefree += 1
                expected = n * (-1) ** (n // 2) if n % 2 else 1 + n
                disc = int(fmpz_poly(coeff).discriminant()) % 8
                factors = len(f.factor()[1])
                if disc != expected % 8 or (factors - n) % 2 != int(disc == 5):
                    raise ArithmeticError(f"{f} has discriminant {disc} mod 8 and {factors} factors")
    print(f"Checked {checked} polynomials through degree {through}, including "
          f"integer discriminants and binary factorizations for all {squarefree} squarefree cases.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--through", type=int, default=31, help="maximum degree to enumerate")
    args = parser.parse_args()
    if args.through < 1:
        parser.error("expected a positive degree")
    check(args.through)
