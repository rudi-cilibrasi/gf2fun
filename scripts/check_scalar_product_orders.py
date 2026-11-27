"""Verify the product-of-trinomials exclusion and the resulting full or partial sparse orders."""

import argparse
import csv
import json
import subprocess
import sys
from io import StringIO
from math import gcd, prod
from pathlib import Path

from flint import fmpz

from check_factor_base import irreducible, polynomial
from check_primo_certificate import check_primo
from check_product_range import certified_primes, prime_index_powers
from check_semiprime_scalar_norms import check_short_images, scalar_counts
from check_two_subfield_norms import TABLES, verify_norm_embeddings


DATA = Path(__file__).resolve().parents[1] / "data"


def check_norm(mask, d, primes, cofactor):
    order = (1 << d)-1
    if (prod(primes)*cofactor != order or gcd(prod(primes),cofactor) != 1
            or not all(fmpz(r).is_prime() for r in primes)):
        raise ValueError(f"invalid decomposition in degree {d}")
    x, f = polynomial(2), polynomial(mask)
    if f.degree() != d or not irreducible(f):
        raise ValueError(f"incorrect norm minimal polynomial in degree {d}")
    if any(z == 1 for _,z in prime_index_powers(x, order, sorted(set(primes)), f)):
        raise ValueError(f"a known prime-power norm component is missing in degree {d}")
    if cofactor > 1 and (fmpz(cofactor).is_probable_prime() or x.pow_mod(prod(primes), f) == 1):
        raise ValueError(f"expected a composite cofactor with a nontrivial projection in degree {d}")


def check_sparse_witness(n, row, gp, trinomials):
    p,q = row["degree_primes"]
    if p not in (3,5) or q <= p or p*q != n or not fmpz(q).is_prime():
        raise ValueError("invalid pair of degree primes")
    h = (1 << p)-1
    if not fmpz(h).is_prime():
        raise ValueError("the smaller group must have just one nonidentity subgroup")
    large, rem = divmod((1 << n)-1, h*((1 << q)-1))
    if rem or gcd(large, h*((1 << q)-1)) != 1:
        raise ValueError("invalid cyclotomic decomposition")
    if n == 3415:
        _, certs = TABLES[n]
        if certified_primes(DATA / certs, {large}, gp) != {large}:
            raise ValueError("missing cyclotomic primality certificate")
    else:
        check_primo(DATA / f"degree-{n}-primality.cert.gz", large, gp)
    support = row["exponents"]
    if support != sorted(set(support)) or support[0] != 0 or support[-1] != n or len(support) not in (3,5):
        raise ValueError("incorrect sparse witness")
    masks = {int(d):int(mask,16) for d,mask in row["norm_polynomials"].items()}
    if set(masks) != {p,q}:
        raise ValueError("missing subfield norm")
    verify_norm_embeddings(support,masks,gp)
    primes = row["known_large_subfield_primes"]
    cofactor = int(row["large_subfield_cofactor"])
    check_norm(masks[p],p,[h],1)
    check_norm(masks[q],q,primes,cofactor)

    if n == 3415:
        check_short_images(n,[row],row["short_power_images"])
        factors = [h,*primes,large]
        inp = " ".join(map(str,[n,len(factors),*factors]))+"\n"
        proc = subprocess.run([trinomials],input=inp,text=True,capture_output=True,check=True)
        taps = " ".join(map(str,row["irreducible_trinomial_taps"]))
        if list(csv.DictReader(StringIO(proc.stdout))) != [
                {"degree":str(n),"irreducible_taps":taps,"primitive_taps":taps}]:
            raise ValueError("trinomial census disagreement")
    return large, cofactor


def check(n, row, binary, gp, trinomials):
    p,q = row["degree_primes"]
    counts = scalar_counts(binary,p,q,(1 << p)-1)
    if counts != row["product_counts"] or counts[-1] != 0:
        raise ValueError(f"split support census failed in degree {n}")
    large, cofactor = check_sparse_witness(n,row,gp,trinomials)
    status = "primitive" if cofactor == 1 else f"index divides the {len(str(cofactor))}-digit cofactor"
    print(f"Degree {n}: {counts[1]:,} possible supports, no split roots, "
          f"{len(str(large))}-digit prime forced. Witness {row['exponents']}, {status}.", flush=True)


if __name__ == "__main__":
    if hasattr(sys,"set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp",default="gp")
    parser.add_argument("--products",required=True,help="compiled scripts/check_scalar_pair_products.cpp")
    parser.add_argument("--trinomials",required=True,help="compiled scripts/prime_degree_trinomials.cpp")
    parser.add_argument("--degree",type=int,help="verify one table entry")
    args = parser.parse_args()
    rows = json.loads((DATA / "scalar-pair-products.json").read_text())
    if args.degree is not None and str(args.degree) not in rows:
        parser.error("degree is outside the table")
    if scalar_counts(args.products,2,5,3) != [1,45,5,2,2,4]:
        raise ArithmeticError("failed the positive control from the factorization of X^93+1")
    for key,row in rows.items():
        if args.degree is None or args.degree == int(key):
            check(int(key),row,args.products,args.gp,args.trinomials)
