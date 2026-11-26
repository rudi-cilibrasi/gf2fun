"""Verify the degree-1229 Frobenius models over F_4 and their common sparse-root coordinates."""

import argparse
import csv
import gzip
import json
import subprocess
from math import gcd
from pathlib import Path

from flint import fq_default_ctx, fq_default_poly_ctx

from check_degree_1229 import COFACTOR, GROUP, KNOWN, PRIMES
from check_factor_base import DATA, polynomial
from period_coordinate import CANDIDATES, DEGREE, mask_of, period_polynomial


MODELS = DATA / "degree-1229-quaternary-models.json"


def verify(row, old):
    constants = fq_default_ctx(2, 2, "w")
    ring = fq_default_poly_ctx(constants)
    t = ring.gen()
    four = [constants([n & 1, n >> 1]) for n in range(4)]
    q, a, b = row["q"], row["numerator"], row["denominator"]
    if q not in (256, 512) or len(a) != len(b) or row["id"] != sum(c << (2*i) for i, c in enumerate(a+b)):
        raise ArithmeticError("wrong model parameters")
    h0, h1 = ring([four[c] for c in a]), ring([four[c] for c in b])
    packed = int(row["relative_modulus_packed_hex"], 16)
    g = ring([four[(packed >> (2*i)) & 3] for i in range(DEGREE+1)])
    if (packed >> (2*(DEGREE+1)) or g.degree() != DEGREE or not g.leading_coefficient().is_one()
            or not g.is_irreducible() or not h0.gcd(h1).is_one()
            or (h0(t**q)+t*h1(t**q)) % g != 0):
        raise ArithmeticError("the relative modulus or the Frobenius equation failed")
    binary = polynomial(int(row["binary_modulus_hex"], 16))
    norm = g*ring([c*c for c in g])
    if (binary.degree() != 2*DEGREE or norm != ring([four[int(c)] for c in binary])
            or binary.factor()[1] != [(binary, 1)]):
        raise ArithmeticError("the binary modulus is not the irreducible coefficient norm")
    z = polynomial(int(row["constant_generator_hex"], 16))
    if (z*z+z+1) % binary != 0:
        raise ArithmeticError("incorrect F_4 constant")
    even = polynomial(sum(((packed >> (2*i)) & 1) << i for i in range(DEGREE+1)))
    odd = polynomial(sum(((packed >> (2*i+1)) & 1) << i for i in range(DEGREE+1)))
    if (even+z*odd) % binary != 0:
        raise ArithmeticError("the two presentations use different constant embeddings")
    per = polynomial(int(row["period_hex"], 16))
    gen = polynomial(int(row["certified_generator_hex"], 16))
    if (period_polynomial(DEGREE).compose_mod(per, binary) != 0
            or polynomial(int(old["modulus_hex"], 16)).compose_mod(gen, binary) != 0
            or polynomial(int(old["period_hex"], 16)).compose_mod(gen, binary) != per):
        raise ArithmeticError("the primitive generator and period embeddings disagree")
    for name, taps in CANDIDATES.items():
        r = polynomial(int(row["sparse_root_hex"][name], 16))
        if (polynomial(int(old["sparse_root_hex"][name], 16)).compose_mod(gen, binary) != r
                or 1+sum((r.pow_mod(i, binary) for i in (*taps, DEGREE)), polynomial(0)) != 0):
            raise ArithmeticError(f"invalid embedding of the {name} root")
    if row["id"] == 21149:
        x = polynomial(2)
        norm = x*x.pow_mod(1 << DEGREE, binary) % binary
        anchor = norm.pow_mod(9, binary)
        if (anchor.pow_mod(GROUP, binary) != 1 or anchor.pow_mod(KNOWN, binary) == 1
                or any(anchor.pow_mod(GROUP//p, binary) == 1 for p in PRIMES)):
            raise ArithmeticError("the quaternary anchor failed a known order projection")
    return binary, gen


def verify_logarithms(model, backend):
    modulus = (1 << 18)-1
    labels = set()
    z = 1
    powers = [0]*modulus
    for i in range(modulus):
        powers[i] = z
        z <<= 1
        if z >> 18:
            z ^= 0x41403
    if z != 1 or len(set(powers)) != modulus:
        raise ArithmeticError("the binary polynomial does not generate the eighteen-bit constants")
    for i in range(modulus):
        labels.add(min(powers[(i*(4**j)) % modulus] for j in range(9)))
    labels.add(0)
    lines = [" ".join(map(str, (int(model["binary_modulus_hex"], 16), int(model["constant_generator_hex"], 16),
                                KNOWN, COFACTOR)))]
    with gzip.open(DATA/"degree-1229-q512-quaternary-logs.csv.gz", "rt", newline="") as stream:
        rows = csv.DictReader(stream)
        if rows.fieldnames != ["mask", "exponent"]:
            raise ValueError("incorrect q=512 logarithm header")
        for t in sorted(labels):
            row = next(rows)
            e = int(row["exponent"])
            if (int(row["mask"], 0) != t or not 0 <= e < COFACTOR
                    or gcd(e, COFACTOR) != 1 or (t == 0 and e != 1)):
                raise ValueError("incorrect label, exponent or anchor normalization")
            lines.append(f"{t} {e}")
        if next(rows, None) is not None or len(labels) != 29144:
            raise ValueError("incorrect size of the q=512 logarithm table")
    subprocess.run([str(backend.resolve())], input="\n".join(lines)+"\n", text=True, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=int, help="select a packed coefficient pair")
    parser.add_argument("--task", choices=CANDIDATES, help="export a sparse-root task in the absolute binary presentation")
    parser.add_argument("--verify-logs", type=Path, metavar="NTL_BACKEND", help="check every q=512 projected norm exponent")
    args = parser.parse_args()
    selected = args.model if args.model is not None else (21149 if args.task or args.verify_logs else None)
    if args.verify_logs and selected != 21149:
        parser.error("the norm logarithm table uses model 21149")
    rows = [r for r in json.loads(MODELS.read_text()) if selected is None or r["id"] == selected]
    if not rows:
        parser.error("unrecognized model")
    old = next(r for r in json.loads((DATA/"degree-1229-frobenius-models.json").read_text()) if r["q"] == 1024)
    for row in rows:
        field, generator = verify(row, old)
        if args.verify_logs:
            verify_logarithms(row, args.verify_logs)
        if args.task:
            r = polynomial(int(row["sparse_root_hex"][args.task], 16))
            print(json.dumps({"model": row["id"], "q": row["q"], "candidate": args.task,
                              "modulus_hex": row["binary_modulus_hex"], "K": str(KNOWN), "C": str(COFACTOR),
                              "base_hex": hex(mask_of(generator.pow_mod(KNOWN, field))),
                              "target_hex": hex(mask_of(r.pow_mod(KNOWN, field)))}, indent=2))
        else:
            print(f"q={row['q']}, model {row['id']}: degree-1229 quaternary and degree-2458 binary fields, "
                  "primitive generator and both pentanomial embeddings verified.")


if __name__ == "__main__":
    main()
