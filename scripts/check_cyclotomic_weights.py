"""Verify the exceptional root orders and the cyclotomic weight spectra in three prime degrees."""

import argparse
import json
import subprocess
from pathlib import Path

from flint import fmpz

from check_product_range import certified_primes


DATA = Path(__file__).resolve().parents[1] / "data"
# Interior taps of an irreducible defining polynomial, and the ECPP archive if needed.
FIELDS = {
    1637: ([26, 51, 77], None),
    3359: ([15, 20, 35], "mersenne-3201-3456-prime-certificates.json.gz"),
    4243: ([435, 870, 3808], "mersenne-prime-degrees-ecpp.json.gz"),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", default="cyclotomic_weight_census", help="compiled NTL census")
    parser.add_argument("--gp", default="gp", help="PARI/GP executable for the ECPP certificates")
    args = parser.parse_args()
    rows = json.loads((DATA / "cyclotomic-weight-spectra.json").read_text())
    if [row["degree"] for row in rows] != list(FIELDS):
        raise ValueError("unexpected degree list")
    for row in rows:
        n, s = row["degree"], row["prime"]
        taps, archive = FIELDS[n]
        p, remainder = divmod((1 << n) - 1, s)
        if remainder or p <= s or not fmpz(s).is_prime():
            raise ValueError(f"incorrect group order factors at degree {n}")
        if archive:
            if certified_primes(DATA / archive, {p}, args.gp) != {p}:
                raise ValueError(f"missing large-prime proof at degree {n}")
        elif not fmpz(p).is_prime():
            raise ValueError(f"large cofactor is composite at degree {n}")
        result = subprocess.run([args.census, *map(str, [n, s, *taps])], text=True,
                                capture_output=True, check=True)
        if json.loads(result.stdout) != row or row["additive_intersection"] != 0:
            raise ValueError(f"cyclotomic census disagreement at degree {n}")
        minimum = min(map(int, row["weights"]))
        orbit_min = min(minimum, min(map(int, row["translated_weights"])))
        print(f"Degree {n}: all {sum(row['weights'].values())} factors verified. "
              f"Minimum weight {minimum}, six-image minimum {orbit_min}.", flush=True)


if __name__ == "__main__":
    main()
