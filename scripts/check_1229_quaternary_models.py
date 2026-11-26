"""Verify the degree-1229 Frobenius models over F_4 and their common sparse-root coordinates."""

import argparse
import csv
import gzip
import json
import subprocess
from collections import Counter
from math import gcd, prod
from pathlib import Path

from flint import fq_default_ctx, fq_default_poly_ctx

from check_degree_1229 import COFACTOR, GROUP, KNOWN, PRIMES
from check_factor_base import DATA, irreducible, polynomial
from period_coordinate import CANDIDATES, DEGREE, mask_of, period_polynomial


MODELS = DATA / "degree-1229-quaternary-models.json"
RANK = DATA / "degree-1229-q1024-quaternary-rank.json"


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
        certificate = json.loads(RANK.read_text())
        mask = int(certificate["norm_minimal_polynomial_hex"], 16)
        minimal = polynomial(mask)
        if (minimal.degree() != DEGREE or not irreducible(minimal) or minimal.compose_mod(norm, binary) != 0
                or mask.bit_count() != certificate["norm_minimal_polynomial_weight"]):
            raise ArithmeticError("incorrect binary minimal polynomial of the norm generator")
    return binary, gen


def order_census(output, labels):
    indices = Counter()
    exceptions = {}
    lightest, weight = [], DEGREE+1
    for label, line in zip(sorted(labels), output.splitlines(), strict=True):
        mask, flags, terms = map(int, line.split())
        if mask != label or not 0 <= flags < 1 << len(PRIMES) or not 1 <= terms <= DEGREE+1 or terms % 2 == 0:
            raise ValueError("invalid quaternary norm order or weight row")
        index = prod(p for i, p in enumerate(PRIMES) if flags >> i & 1)
        indices[str(index)] += 1
        if index > 1:
            exceptions[hex(label)] = str(index)
        elif terms <= weight:
            if terms < weight:
                lightest = []
                weight = terms
            lightest.append(hex(label))
    return {"indices": dict(indices), "imprimitive_labels": exceptions,
            "minimum_primitive_weight": weight, "lightest_primitive_labels": lightest}


def verify_logarithms(model, backend, orders=False):
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
    if orders:
        lines.append(" ".join(map(str, PRIMES)))
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
    command = [str(backend.resolve())] + (["--orders"] if orders else [])
    proc = subprocess.run(command, input="\n".join(lines)+"\n", text=True, check=True,
                          stdout=subprocess.PIPE if orders else None)
    if orders:
        summary = order_census(proc.stdout, labels)
        if summary != json.loads((DATA / "degree-1229-q512-quaternary-orders.json").read_text()):
            raise ArithmeticError("the exact order and minimum-weight census differs")
        print(json.dumps(summary, indent=2))


def sparse_task(row, old, field, generator, name, norm_base, exponent):
    if name == "seventh-power":
        from check_1229_power_images import SOURCE, verify_pair
        from prepare_1229_single_log import prepare

        f = verify_pair()
        _, model, _, root = prepare(SOURCE)
        if mask_of(model) != int(old["modulus_hex"], 16):
            raise ValueError("the seventh-power root uses a different binary model")
        r = root.compose_mod(generator, field)
        if f.compose_mod(r, field) != 0:
            raise ArithmeticError("the seventh-power source embedding failed")
    else:
        r = polynomial(int(row["sparse_root_hex"][name], 16))
    if norm_base:
        x = polynomial(2)
        generator = (x*x.pow_mod(1 << DEGREE, field) % field).pow_mod(9, field)
    base = generator.pow_mod(KNOWN, field)
    target = r.pow_mod(KNOWN, field)
    result = {"model": row["id"], "q": row["q"], "candidate": name,
              "modulus_hex": row["binary_modulus_hex"], "K": str(KNOWN), "C": str(COFACTOR),
              "base_hex": hex(mask_of(base)), "target_hex": hex(mask_of(target))}
    if norm_base:
        result["normalization"] = "q512-quaternary-norm-at-zero"
    if exponent is not None:
        if not 0 <= exponent < COFACTOR or base.pow_mod(exponent, field) != target:
            raise ValueError("the submitted exponent fails the projected field equality")
        if r.pow_mod(GROUP, field) != 1 or any(r.pow_mod(GROUP//p, field) == 1 for p in PRIMES):
            raise ArithmeticError("the sparse root fails a known prime-index test")
        result["exact_index"] = str(gcd(exponent, COFACTOR))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=int, help="select a packed coefficient pair")
    parser.add_argument("--task", choices=[*CANDIDATES, "seventh-power"],
                        help="export a sparse-root task in the absolute binary presentation")
    parser.add_argument("--norm-base", action="store_true", help="use the base of the solved q=512 norm table")
    parser.add_argument("--log", type=int, help="verify a task exponent and compute the exact index")
    parser.add_argument("--verify-logs", type=Path, metavar="NTL_BACKEND", help="check every q=512 projected norm exponent")
    parser.add_argument("--orders", action="store_true", help="check the full order and weight of all 29,144 norms")
    args = parser.parse_args()
    if (args.norm_base or args.log is not None) and not args.task:
        parser.error("--norm-base and --log require --task")
    selected = args.model if args.model is not None else (21149 if args.task or args.verify_logs else None)
    if args.verify_logs and selected != 21149:
        parser.error("the norm logarithm table uses model 21149")
    if args.norm_base and selected != 21149:
        parser.error("the primitive norm base is certified in model 21149")
    if args.orders and not args.verify_logs:
        parser.error("--orders requires --verify-logs NTL_BACKEND")
    rows = [r for r in json.loads(MODELS.read_text()) if selected is None or r["id"] == selected]
    if not rows:
        parser.error("unrecognized model")
    old = next(r for r in json.loads((DATA/"degree-1229-frobenius-models.json").read_text()) if r["q"] == 1024)
    for row in rows:
        field, generator = verify(row, old)
        if args.verify_logs:
            verify_logarithms(row, args.verify_logs, args.orders)
        if args.task:
            task = sparse_task(row, old, field, generator, args.task, args.norm_base, args.log)
            print(json.dumps(task, indent=2))
        else:
            print(f"q={row['q']}, model {row['id']}: degree-1229 quaternary and degree-2458 binary fields, "
                  "primitive generator and both pentanomial embeddings verified.")


if __name__ == "__main__":
    main()
