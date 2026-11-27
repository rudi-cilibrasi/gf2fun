"""Compare the cubic character of a twisted cyclotomic root with a certified ray class number."""

import argparse
import subprocess

from flint import fmpz

from check_translation_lift_orders import X, cyclotomic_form


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
    commands = [function, *(f'print(raytwo({p}));' for p in primes)]
    run = subprocess.run([gp, "-qf"], input="\n".join(commands) + "\n",
                         text=True, capture_output=True, check=True)
    values = [int(line) for line in run.stdout.splitlines()]
    if run.stderr or len(values) != len(primes):
        raise ValueError(f"incomplete certified ray class numbers: {run.stderr}")
    cubes = []
    for p, h in zip(primes, values):
        root_is_cube = X.pow_mod(((1 << (p - 1)) - 1) // 3, cyclotomic_form(p)) == 1
        if root_is_cube != (h % 3 == 0):
            raise ValueError(f"cubic character mismatch for p={p}, h(4p)={h}")
        if root_is_cube:
            cubes.append(p)
    print(f"Certified {len(primes)} ray class numbers and binary cubic characters through p=2053.")
    print(f"The {len(cubes)} cube cases have p in {cubes}.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="PARI/GP executable")
    check(parser.parse_args().gp)
