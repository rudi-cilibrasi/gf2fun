"""Check root orders for pentanomials containing three consecutive exponents."""

import json
from math import prod
from pathlib import Path

from flint import fmpz

from check_factor_base import irreducible, modulus, polynomial
from check_product_range import prime_index_powers


DATA = Path(__file__).resolve().parents[1] / "data"


def check_order(n, tap, order, primes):
    f = modulus(n, (1, 2, tap))
    x = polynomial(2)
    if prod(primes) != order or not all(fmpz(p).is_prime() for p in set(primes)):
        raise ArithmeticError(f"incomplete order factorization in degree {n}")
    if not irreducible(f) or x.pow_mod(order, f) != 1:
        raise ArithmeticError(f"degree or order test failed in degree {n}")
    if any(value == 1 for _, value in prime_index_powers(x, order, sorted(set(primes)), f)):
        raise ArithmeticError(f"a proper divisor is an order in degree {n}")


def main():
    check_order(6, 4, 21, [3, 7])
    print("Degree 6 has a split root of exact order 21 with taps 1, 2 and 4.")
    for n, tap, table in ((1233, 43, "mersenne-1230-1280-factors.json"),
                          (3375, 491, "mersenne-3201-3456.json")):
        factors = json.loads((DATA / table).read_text())[str(n)]
        check_order(n, tap, (1 << n) - 1, factors)
        print(f"Degree {n} is primitive with taps 1, 2 and {tap}.")


if __name__ == "__main__":
    main()
