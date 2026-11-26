"""Verify all 52,488 projected 943-bit discrete logarithms and unconditional primitivity of the
degree-1229 q=1024 Frobenius modulus I(X) without factoring the 284-digit cofactor C of 2^1229 - 1.

Checks:
  1. SHA-256 and completeness of data/degree-1229-q1024-projected-logs.csv.gz (all 52,488 monic
     irreducible binary polynomials of degree dividing 20, sum d*N_d = 2^20).
  2. Irreducibility of I(X) (degree 1229, h0 = T^5+T^2+1, h1 = T^3+T, q = 1024) and the four
     known prime-factor order tests + x^K != 1.
  3. gcd(e_P, C) == 1 for all 52,488 exponents (proving every P(x)^K has full cofactor order C).
  4. Direct verification in F_{2^1229} = F_2[X]/(I(X)):
         (x^K)^{e_P} == P(x)^K (mod I(X))
     and irreducibility of P for every entry (supports --sample N for quick smoke checks, default: all 52,488).
  5. Exact rational Weil character-sum bounds (Theorem thm:factor-moments, c_0 = c_20 = c_40 = 1):
     - Standalone 1-trial-division bound (C % 2459 != 0 => J >= 9833): Q = 1294.9018... > 1227.
     - Wheel bound (J = 818085338814611458): Q = 1366.0013... > 1227.
"""
import argparse
import csv
import gzip
import hashlib
import json
import time
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from math import gcd, prod
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
COFACTOR, REM = divmod(GROUP, KNOWN)
assert REM == 0

WHEEL_BOUND = 818085338814611457
INDEX_FLOOR_WHEEL = WHEEL_BOUND + 1

REPO_ROOT = Path(__file__).resolve().parent.parent


def poly_from_mask(mask: int) -> nmod_poly:
    return nmod_poly([(mask >> i) & 1 for i in range(mask.bit_length())], 2)


def is_irred_f2(p: nmod_poly) -> bool:
    facs = p.factor()[1]
    return len(facs) == 1 and facs[0][1] == 1


def weil_bound_Q(index_floor: int) -> Fraction:
    b20 = 1 << 20
    term20 = Fraction(2, 1 << 10) * (1 + b20)
    term40 = Fraction(1, 1 << 20) * (1 + b20 - Fraction((1 << 40) - b20, index_floor - 1))
    return Fraction(2, 3) * (term20 + term40)


_I = None
_BASE = None


def _init_worker(mod_hex: str) -> None:
    global _I, _BASE
    _I = poly_from_mask(int(mod_hex, 16))
    x = nmod_poly([0, 1], 2)
    _BASE = x.pow_mod(KNOWN, _I)


def _verify_chunk(items):
    checked = 0
    for mask, exp in items:
        P = poly_from_mask(mask)
        if not is_irred_f2(P):
            return (False, mask, -1)
        if _BASE.pow_mod(exp, _I) != P.pow_mod(KNOWN, _I):
            return (False, mask, exp)
        checked += 1
    return (True, checked, 0)


def main() -> None:
    ap = argparse.ArgumentParser(description="Verify degree-1229 q=1024 projected discrete logs and primitivity.")
    ap.add_argument("--jobs", type=int, default=8, help="Parallel worker processes (default: 8)")
    ap.add_argument("--sample", type=int, default=0, help="If >0, check only first N entries in F_{2^1229} (0 = all 52,488)")
    args = ap.parse_args()

    t0 = time.time()
    csv_path = REPO_ROOT / "data" / "degree-1229-q1024-projected-logs.csv.gz"
    cert_path = REPO_ROOT / "data" / "degree-1229-q1024-certificate.json"
    models_path = REPO_ROOT / "data" / "degree-1229-frobenius-models.json"

    cert = json.loads(cert_path.read_text())
    sha = hashlib.sha256(csv_path.read_bytes()).hexdigest()
    assert sha == cert["csv_gz_sha256"], f"SHA-256 mismatch: {sha} != {cert['csv_gz_sha256']}"

    models = json.loads(models_path.read_text())
    rec = [r for r in models if r["q"] == 1024][0]
    mod_hex = rec["modulus_hex"]
    assert mod_hex == cert["modulus_hex"]

    pairs = []
    with gzip.open(csv_path, "rt") as gz:
        rd = csv.reader(gz)
        hdr = next(rd)
        assert hdr == ["mask", "exponent"]
        for m_s, e_s in rd:
            m, e = int(m_s), int(e_s)
            assert 0 <= e < COFACTOR
            assert gcd(e, COFACTOR) == 1, f"Non-trivial gcd(e_P, C) at mask={m}"
            pairs.append((m, e))

    N = len(pairs)
    assert N == 52488, f"Expected 52488 rows, got {N}"
    masks = [m for m, _ in pairs]
    assert pairs[0] == (2, 1), f"Expected anchor (2, 1), got {pairs[0]}"
    deg_counts = Counter(m.bit_length() - 1 for m in masks)
    expected_counts = {1: 2, 2: 1, 4: 3, 5: 6, 10: 99, 20: 52377}
    assert len(set(masks)) == N and dict(deg_counts) == expected_counts
    assert sum(d * cnt for d, cnt in deg_counts.items()) == (1 << 20)
    print(f"Loaded & audited {N} rows (SHA-256 verified, all gcd(e_P, C) == 1) in {time.time()-t0:.2f}s.")

    I = poly_from_mask(int(mod_hex, 16))
    assert I.degree() == 1229 and is_irred_f2(I)
    x = nmod_poly([0, 1], 2)
    assert x.pow_mod(GROUP, I) == 1
    assert x.pow_mod(KNOWN, I) != 1
    for p in PRIMES:
        assert x.pow_mod(GROUP // p, I) != 1
    print("Verified I(X) is irreducible of degree 1229 and passes all 4 known prime-factor order tests + x^K != 1.")

    target_pairs = pairs[: args.sample] if args.sample > 0 else pairs
    t1 = time.time()
    workers = max(1, args.jobs)
    chunks = [target_pairs[i::workers] for i in range(workers)]
    total_ok = 0
    with ProcessPoolExecutor(max_workers=workers, initializer=_init_worker, initargs=(mod_hex,)) as ex:
        for ok, val1, val2 in ex.map(_verify_chunk, chunks):
            if not ok:
                raise AssertionError(f"Direct field check FAILED for mask={val1}, exp={val2}")
            total_ok += val1
    assert total_ok == len(target_pairs)
    print(f"Directly verified irreducibility + {total_ok}/{len(target_pairs)} projected discrete logs in F_{{2^1229}} in {time.time()-t1:.2f}s.")

    # Self-contained 1-trial-division bound (p == 1 mod 2458; 4917 = 3*1639, 7375 = 5^3*59; C % 2459 != 0 => p >= 9833)
    assert 4917 % 3 == 0 and 7375 % 5 == 0 and COFACTOR % 2459 != 0
    Q_standalone = weil_bound_Q(9833)
    Q_wheel = weil_bound_Q(INDEX_FLOOR_WHEEL)
    assert Q_standalone > 1227 and Q_wheel > 1227
    print(f"Standalone 1-trial-division Weil bound (J >= 9833): Q = {float(Q_standalone):.6f} > 1227")
    print(f"Wheel-assisted Weil bound (J >= {INDEX_FLOOR_WHEEL}): Q = {float(Q_wheel):.6f} > 1227")
    if args.sample == 0:
        print("UNCONDITIONALLY CERTIFIED: I(X) is primitive of exact order 2^1229 - 1 without factoring C!")


if __name__ == "__main__":
    main()
