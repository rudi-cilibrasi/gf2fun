"""Standalone single-scalar primitivity verifier for any degree-1229 irreducible polynomial P(Y).

Because data/degree-1229-q1024-projected-logs.csv.gz unconditionally certifies that the q=1024
Frobenius coordinate x (minimal polynomial I(X)) has exact multiplicative order 2^1229 - 1,
proving primitivity of ANY degree-1229 irreducible polynomial P(Y) (for example, any of the
639,144 eligible degree-1229 pentanomials) reduces from 3,380 (or 52,488) open discrete logs to
exhibiting ONE single integer e_r in [0, C) such that:
    (Y^K)^{e_r} == x_in_P^K  (mod P(Y)),
where I(x_in_P) == 0 (mod P(Y)) and Y passes the four known prime-factor order tests.
"""
import argparse
import json
from math import prod
from pathlib import Path

from flint import nmod_poly

PRIMES = (
    36871,
    46703,
    10543179280661916121033,
    9536289355314392579996071515160583098298616686033085857,
)
KNOWN = prod(PRIMES)
GROUP = (1 << 1229) - 1
COFACTOR = GROUP // KNOWN
REPO_ROOT = Path(__file__).resolve().parent.parent


def poly_from_mask(mask: int) -> nmod_poly:
    return nmod_poly([(mask >> i) & 1 for i in range(mask.bit_length())], 2)


def poly_from_taps(deg: int, taps: list[int]) -> nmod_poly:
    c = [0] * (deg + 1)
    c[0] = 1
    c[deg] = 1
    for t in taps:
        c[t] ^= 1
    return nmod_poly(c, 2)


def eval_poly_mod(F: nmod_poly, x_elem: nmod_poly, modP: nmod_poly) -> nmod_poly:
    res = nmod_poly([0], 2)
    one = nmod_poly([1], 2)
    for i in range(F.degree(), -1, -1):
        res = (res * x_elem) % modP
        if int(F[i]):
            res = res + one
    return res


def verify_single_scalar(P: nmod_poly, x_elem: nmod_poly, e_r: int, cert_path: Path) -> None:
    cert = json.loads(cert_path.read_text())
    I = poly_from_mask(int(cert["modulus_hex"], 16))
    # Only the unique degree-1229 irreducible factor of this parent has the
    # published full-order proof. Bind even a custom metadata path to that field.
    Y = nmod_poly([0, 1], 2)
    t = Y**1024
    parent = t**5 + t**2 + 1 + Y*(t**3 + t)
    if I.degree() != 1229 or parent % I != 0 or I.factor()[1] != [(I, 1)]:
        raise ValueError("the supplied modulus is not the certified q=1024 generator polynomial")
    facs = P.factor()[1]
    if P.degree() != 1229 or len(facs) != 1 or facs[0][1] != 1:
        raise ValueError("P is not irreducible of degree 1229")
    if Y.pow_mod(GROUP, P) != 1:
        raise ArithmeticError("the proposed root fails the field-order test")
    for p in PRIMES:
        if Y.pow_mod(GROUP // p, P) == 1:
            raise ArithmeticError(f"the root order misses the known prime {p}")
    if not eval_poly_mod(I, x_elem % P, P).is_zero():
        raise ArithmeticError("the supplied field element is not a root of the certified modulus")
    if not 0 <= e_r < COFACTOR:
        raise ValueError("exponent outside the projected group range")
    YK = Y.pow_mod(KNOWN, P)
    xK = (x_elem % P).pow_mod(KNOWN, P)
    if YK.pow_mod(e_r, P) != xK:
        raise ArithmeticError("the submitted exponent fails the projected field identity")
    print("CERTIFIED PRIMITIVE: exact multiplicative order 2^1229 - 1 verified from one scalar e_r!")


def selftest(cert_path: Path) -> None:
    """End-to-end selftest using P(Y) = I(Y + 1) (where x = Y + 1, e_r = e_{x+1}^{-1} mod C)."""
    import csv, gzip
    cert = json.loads(cert_path.read_text())
    I = poly_from_mask(int(cert["modulus_hex"], 16))
    Yp1 = nmod_poly([1, 1], 2)
    one = nmod_poly([1], 2)
    I_shift = nmod_poly([0], 2)
    for i in range(I.degree(), -1, -1):
        I_shift = I_shift * Yp1
        if int(I[i]):
            I_shift = I_shift + one
    csv_path = REPO_ROOT / "data" / "degree-1229-q1024-projected-logs.csv.gz"
    e_x1 = None
    with gzip.open(csv_path, "rt") as gz:
        rd = csv.reader(gz)
        next(rd)
        for m_s, e_s in rd:
            if int(m_s) == 3:
                e_x1 = int(e_s)
                break
    assert e_x1 is not None
    e_r = pow(e_x1, -1, COFACTOR)
    verify_single_scalar(I_shift, Yp1, e_r, cert_path)


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="Certify a degree-1229 polynomial primitive from one scalar log e_r.")
    ap.add_argument("--selftest", action="store_true", help="Run E2E verification on P(Y) = I(Y + 1)")
    ap.add_argument("--taps", type=str, help="Comma-separated interior taps of sparse polynomial")
    ap.add_argument("--x-hex", type=str, help="Hex mask of x in F_2[Y]/(P(Y)) with I(x)=0")
    ap.add_argument("--exp", type=str, help="Decimal exponent e_r with (Y^K)^{e_r} == x^K mod P")
    ap.add_argument("--cert", type=str, default=str(REPO_ROOT / "data" / "degree-1229-q1024-certificate.json"))
    args = ap.parse_args()
    if args.selftest:
        selftest(Path(args.cert))
    else:
        assert args.taps and args.x_hex and args.exp, "Specify --selftest or all of --taps, --x-hex, --exp"
        P = poly_from_taps(1229, [int(t) for t in args.taps.split(",")])
        verify_single_scalar(P, poly_from_mask(int(args.x_hex, 16)), int(args.exp), Path(args.cert))
