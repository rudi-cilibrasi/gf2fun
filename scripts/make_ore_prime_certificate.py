"""Generate an independently checkable CoqPrime proof for the 425-digit factor of 2^4095-1."""

import argparse
import json
import subprocess
from concurrent.futures import ThreadPoolExecutor
from itertools import count
from pathlib import Path

from sympy import factorint


CERTIFICATE = Path(__file__).resolve().parents[1] / "data" / "ore-4095-primecert.json"
IMPORTS = """From Coq Require Import ZArith Znumtheory List.
From Coqprime.PrimalityTest Require Import PocklingtonCertificat.
From Coqprime.num Require Import Pock.
Import ListNotations.
Open Scope Z_scope.
"""


def terminal_proof(p, known, lemmas):
    if p in known:
        return known[p]
    factors = {int(q): int(e) for q, e in factorint(p - 1).items()}
    names = {q: terminal_proof(q, known, lemmas) for q in factors}
    a = next(a for a in count(2) if all(pow(a, (p-1) // q, p) != 1 for q in factors))
    name = f"prime_small_{p}"
    factor_list = "; ".join(f"({q},{e})%positive" for q, e in factors.items())
    references = "; ".join(f"Proof_certif {q} {names[q]}" for q in factors)
    lemmas.append(f"""Lemma {name} : prime {p}.
Proof. apply (Pock.Pocklington_refl (SPock_certif {p} {a} [{factor_list}])
  [{references}]). vm_cast_no_check (eq_refl true). Qed.
""")
    known[p] = name
    return name


def generate(rows, directory, jobs):
    directory.mkdir(parents=True, exist_ok=True)
    steps = []
    for i, (n, t, s, a, (x, y)) in enumerate(rows):
        q, rem = divmod(n + 1 - t, s)
        if rem or (i + 1 < len(rows) and rows[i + 1][0] != q):
            raise ValueError("broken elliptic certificate chain")
        b = (y*y - x**3 - a*x) % n
        steps.append(f"""Lemma prime_step_{i} : prime {q} -> prime {n}.
Proof. intro H. apply (Pock.Pocklington_refl (Ell_certif {n} {s} [({q},1)%positive]
  {a % n} {b} {x} {y}) [Proof_certif {q} H]).
  vm_cast_no_check (eq_refl true). Qed.
""")
    batches = []
    for i in range(min(jobs, len(steps))):
        name = f"Ore4095Steps{i:02}"
        (directory / f"{name}.v").write_text(IMPORTS + "\n" + "\n".join(steps[i::jobs]))
        batches.append(name)
    lemmas = []
    terminal = terminal_proof(q, {2: "prime_2"}, lemmas)
    main = ["Require Import " + " ".join(batches) + ".", *lemmas,
            f"Theorem prime_largest_4095_factor : prime {rows[0][0]}.", "Proof."]
    main.extend(f"  apply prime_step_{i}." for i in range(len(rows)))
    main.extend([f"  exact {terminal}.", "Qed.", ""])
    (directory / "Ore4095Prime.v").write_text(IMPORTS + "\n" + "\n".join(main))
    return batches


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, help="directory for the generated Coq sources")
    parser.add_argument("--jobs", type=int, default=4, help="split independent elliptic steps into this many files")
    parser.add_argument("--check", action="store_true", help="compile the proof with coqc and CoqPrime")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    with CERTIFICATE.open() as source:
        modules = generate(json.load(source), args.directory, args.jobs)
    if args.check:
        def compile_module(name):
            subprocess.run(["coqc", "-q", name + ".v"], cwd=args.directory, check=True)

        with ThreadPoolExecutor(max_workers=len(modules)) as pool:
            list(pool.map(compile_module, modules))
        compile_module("Ore4095Prime")
