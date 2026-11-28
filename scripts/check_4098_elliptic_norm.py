"""Certify the two finite-field norms and the cubic order task in degree 4098."""

import argparse
import json
from math import gcd, prod

from flint import fmpz, fq_default_ctx, fq_default_poly_ctx

from check_cubed_parity import X, polynomial
from check_factor_base import DATA


def from_hex(value):
    mask = int(value, 16)
    return polynomial(i for i in range(mask.bit_length()) if mask >> i & 1)


def cubic_order_test(row, q, cofactor, primes):
    field = fq_default_ctx(modulus=from_hex(row["norm_degree_683_hex"]))
    s = field.gen()
    ring = fq_default_poly_ctx(field)
    cubic = ring([s**4098, 1+s+s**2, 1+s, field.one()])
    assert cubic.is_irreducible()
    z = ring.gen().pow_mod(7*(q-1), cubic)
    assert z != 1 and z.pow_mod(cofactor, cubic) == 1
    for p in primes:
        if p < 2 or cofactor % p or not fmpz(p).is_prime():
            raise ValueError(f"{p} is not a prime divisor of C")
        print(f"full {p}-part of the root order: {z.pow_mod(cofactor // p, cubic) != 1}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cubic", action="store_true", help="verify the reduced cubic field directly")
    parser.add_argument("--prime", type=int, action="append", default=[],
                        help="test a supplied prime divisor of C in the reduced cubic field")
    args = parser.parse_args()
    row = json.loads((DATA / "degree-4098-elliptic-norm.json").read_text())
    n = row["degree"]
    q = 2**683
    group = q**6 - 1
    primes = {int(p): e for p, e in row["known_prime_powers"]}
    known = prod(p**e for p, e in primes.items())
    c = int(row["composite_cofactor"])
    assert n == 4098 and known*c == group and gcd(known, c) == 1
    assert all(e >= 1 and fmpz(p).is_prime() for p, e in primes.items())
    assert not fmpz(c).is_prime() and 7*c == q*q + q + 1
    if args.cubic or args.prime:
        cubic_order_test(row, q, c, args.prime)
        print("Verified the cubic over the published degree-683 field and the exponent C.")
        return

    f = polynomial((0, 1, 3, 4096, 4098))
    seed = polynomial((0, 1, 1366))
    assert f.is_irreducible() and seed.is_irreducible()
    assert X.pow_mod(group, f) == 1 and X.pow_mod(known, f) != 1
    assert all(X.pow_mod(group // p, f) != 1 for p in primes)
    subgroup = q*q - 1
    assert gcd(subgroup, c) == gcd(1366, subgroup) == 1
    assert X.pow_mod(subgroup, seed) == 1
    assert all(X.pow_mod(subgroup // p, seed) != 1 for p in primes if subgroup % p == 0)

    u = X + 1
    a = u.pow_mod(3, f)
    s = u.pow_mod(q**3+1, f)
    b = X.pow_mod(q**3+1, f)
    assert seed.compose_mod(a, f) == 0
    assert X.pow_mod(group // subgroup, f) == a.pow_mod(1366, f)
    assert s.pow_mod(q, f) == s and s.pow_mod(3, f) == a.pow_mod(q+1, f)
    assert (b**3 + (1+s)*b**2 + (1+s+s**2)*b + s.pow_mod(n, f)) % f == 0
    assert b.pow_mod(q*q+q+1, f) == s.pow_mod(n, f)
    assert gcd(n, q-1) == 1

    for degree, weight, value in ((683, 351, s), (2049, 1005, b)):
        minimal = from_hex(row[f"norm_degree_{degree}_hex"])
        assert minimal.degree() == degree and sum(map(int, minimal.coeffs())) == weight
        assert minimal.is_irreducible() and minimal.compose_mod(value, f) == 0
    assert b.pow_mod((q**3-1)//7, f) != 1
    print("Verified a primitive degree-1366 seed, a primitive degree-683 norm,")
    print("and the full projection of the pentanomial root to order 2^2049+1.")
    print("The remaining test is whether (b^(Q-1))^7 has exact order C,")
    print("where Q=2^683, C=(Q^2+Q+1)/7, and b satisfies the published cubic.")


if __name__ == "__main__":
    main()
