"""Check the known order factors for every sparse primitive degree-11 Ore seed."""

import argparse
from math import gcd, prod

from flint import fmpz, nmod_poly

from check_ore_components import all_sparse_seeds
from check_ore_lifts import lifted_support
from check_ore_norms import from_support, support


# The remaining 549-digit factor can be left unfactored.
# https://factordb.com/index.php?id=1000000000000002047
KNOWN_PRIMES = (47, 131009, 178481, 724639, 2529391927, 70676429054711,
                618970019642690137449562111)


def census():
    size = 2**2047-1
    known = prod(KNOWN_PRIMES)
    cofactor, rem = divmod(size, known)
    if rem or gcd(known, cofactor) != 1 or not all(fmpz(p).is_prime() for p in KNOWN_PRIMES):
        raise ValueError("invalid partial factorization")
    proper = (2**23-1)*(2**89-1)
    if gcd(proper, cofactor) != 1:
        raise ValueError("the remaining cofactor contains a proper-subfield prime")
    primitive_primes = tuple(p for p in KNOWN_PRIMES if proper % p)
    x = nmod_poly([0, 1], 2)
    rows = []
    for seed in all_sparse_seeds(11):
        taps = support(seed)
        f = from_support(lifted_support(taps))
        if x.pow_mod(size, f) != 1 or x.pow_mod(known, f) == 1:
            raise ValueError(f"failed the full power or the cofactor check for {taps}")
        missing = tuple(p for p in KNOWN_PRIMES if x.pow_mod(size//p, f) == 1)
        rows.append((taps, missing, f))
    return rows, primitive_primes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-rows", action="store_true",
                        help="print the 47th-root masks used in OreIndexFortySeven.lean")
    args = parser.parse_args()
    rows, primitive_primes = census()
    exceptions = [(taps, f) for taps, missing, f in rows if missing == (47,)]
    if len(rows) != 46 or len(exceptions) != 2 or sum(not missing for _, missing, _ in rows) != 44:
        raise ValueError("unexpected partial order census")
    if args.lean_rows:
        size = 2**2047-1
        exponent = pow(47, -1, size//47)
        x = nmod_poly([0, 1], 2)
        output = []
        for taps, f in exceptions:
            w = x.pow_mod(exponent, f)
            if w.pow_mod(47, f) != x:
                raise ValueError("incorrect 47th root")
            mask = sum(int(bit) << i for i, bit in enumerate(w.coeffs()))
            a, b, c = taps[1:-1]
            output.append(f"  (({a}, {b}, {c}), 0x{mask:x})")
        print(",\n".join(output))
    else:
        print("46 lifts checked; 44 have all seven known order factors.")
        for taps, _ in exceptions:
            print(f"Seed {taps}: index divisible by 47.")
        print(f"Every order contains {primitive_primes} and a prime of the remaining cofactor.")


if __name__ == "__main__":
    main()
