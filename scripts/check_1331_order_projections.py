"""Verify partial orders in degrees 1331, 3993 and 6655 and isolate the common cofactor."""

import argparse
import json
from math import gcd, prod
from pathlib import Path

from flint import fmpz

from batch_degree_1229 import block_product
from check_factor_base import irreducible, modulus, polynomial
from check_product_range import certified_primes, prime_index_powers


DATA = Path(__file__).resolve().parents[1] / "data"


def check_composite(cofactor, degree, block):
    if degree % 2 == 0 or ((1 << degree) - 1) % cofactor:
        raise ValueError(f"incorrect binary field for the degree-{degree} cofactor")
    if gcd(3, cofactor) != 1 or pow(3, cofactor - 1, cofactor) == 1:
        raise ValueError(f"the base-three compositeness witness failed at {degree}")
    for prime, _ in fmpz(degree).factor():
        if gcd(cofactor, (1 << (degree // int(prime))) - 1) != 1:
            raise ValueError(f"a cofactor prime can lie in a proper subfield at {degree}")
    step = 2 * degree
    k = block["log_block"]
    residue = block_product(cofactor, step, k, method="lagrange")
    if residue != block["residue"] or gcd(residue, cofactor) != 1:
        raise ValueError(f"divisor progression failed in degree {degree}")
    return 1 + step * (1 << (2*k))


def main(gp):
    data = json.loads((DATA / "degree-1331-order-projections.json").read_text())
    d, shared_primes = data["shared_degree"], data["shared_primes"]
    if d != 1331 or not all(fmpz(p).is_prime() for p in shared_primes):
        raise ValueError("incorrect common degree or prime list")
    shared, rem = divmod((1 << d) - 1, prod(shared_primes))
    if rem:
        raise ValueError("incorrect factorization of the degree-1331 group order")
    blocks = data["divisor_progressions"]
    shared_bound = check_composite(shared, d, blocks[str(d)])
    expected = [(1331, "none"), (3993, "prime"), (6655, "composite")]
    if [(row["degree"], row["remaining"]) for row in data["cases"]] != expected:
        raise ValueError("unexpected degree or cofactor description")

    x = polynomial(2)
    for row in data["cases"]:
        n, taps = row["degree"], row["taps"]
        group_order = (1 << n) - 1
        primes = shared_primes + row["additional_primes"]
        if not all(fmpz(p).is_prime() for p in row["additional_primes"]):
            raise ValueError(f"composite factor in the known part at {n}")
        last, rem = divmod(group_order, shared * prod(primes))
        if rem:
            raise ValueError(f"group order is not divisible by the listed factors at {n}")
        composites = [shared]
        bounds = [shared_bound]
        if row["remaining"] == "prime":
            archive = DATA / "degree-3993-prime-certificate.json.gz"
            if certified_primes(archive, {last}, gp) != {last}:
                raise ValueError("missing certificate for the 697-digit prime")
            primes.append(last)
        elif row["remaining"] == "composite":
            composites.append(last)
            bounds.append(check_composite(last, n, blocks[str(n)]))
        elif last != 1:
            raise ValueError(f"unaccounted cofactor at {n}")
        factors = primes + composites
        if any(gcd(v, group_order // v) != 1 for v in factors):
            raise ValueError(f"factor blocks overlap at {n}")

        f = modulus(n, taps)
        if not (taps[:2] == [1, 2] and len(taps) == 3 and 2 < taps[2] < n
                and irreducible(f) and x.pow_mod(group_order, f) == 1):
            raise ValueError(f"incorrect sparse field at {n}")
        components = dict(prime_index_powers(x, group_order, factors, f))
        if any(value == 1 for value in components.values()):
            raise ValueError(f"trivial prime or composite projection at {n}")
        lower = polynomial(int(row["shared_component_polynomial_hex"], 16))
        if (lower.degree() != d or not irreducible(lower)
                or lower.compose_mod(components[shared], f) != 0 or x.pow_mod(shared, lower) != 1):
            raise ValueError(f"incorrect degree-1331 projection at {n}")
        known = prod(primes)
        small = (1 << (n // 11)) - 1
        if known % small or gcd(small, group_order // small) != 1:
            raise ValueError(f"the degree-{n // 11} norm is not certified at {n}")
        print(f"Degree {n}: {len(str(known))}-digit divisor, root order exceeds "
              f"2^{(known * prod(bounds)).bit_length()-1}, index one or above {min(bounds)}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for the ECPP certificate")
    main(parser.parse_args().gp)
