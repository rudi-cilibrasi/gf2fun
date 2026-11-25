"""Check the known and unresolved parts of the degree-1229 root order, or emit its Lean certificate."""

import argparse
from math import gcd, prod

from flint import fmpz, nmod_poly
from make_witnesses import emit_modular_power, prime_certificates

N, U, V = 1229, 27, 50
PRIMES = (36871, 46703, 10543179280661916121033, 9536289355314392579996071515160583098298616686033085857)
KNOWN = prod(PRIMES)
GROUP = (1 << N) - 1
COFACTOR, REMAINDER = divmod(GROUP, KNOWN)


def check(bound):
    if REMAINDER or gcd(KNOWN, COFACTOR) != 1 or not all(fmpz(p).is_prime() for p in PRIMES):
        raise ValueError("incorrect known factors")
    if fmpz(COFACTOR).is_prime():
        raise ValueError("the unresolved factor is prime")
    x = nmod_poly([0, 1], 2)
    f = x**N + x**(U+V) + x**V + x**U + 1
    if x.pow_mod(GROUP, f) != 1 or any(x.pow_mod(GROUP//d, f) == 1 for d in (*PRIMES, COFACTOR)):
        raise ValueError("failed a polynomial order test")
    for candidate in range(2*N+1, bound+1, 2*N):
        if COFACTOR % candidate == 0:
            raise ValueError(f"found a new divisor {candidate}")
    print(f"The unresolved cofactor is {COFACTOR}.")
    print(f"The root order is {KNOWN} times a divisor of the {len(str(COFACTOR))}-digit cofactor.")
    print(f"Every prime of that cofactor exceeds {bound}. The root order exceeds 2^{(KNOWN*bound).bit_length()-1}.")


def emit():
    print("import GF2Sparse.PartialOrder\nimport GF2Sparse.Table")
    print("\n/-! Partial order certificate for the first degree beyond the complete consecutive CSV. -/")
    print("\nnamespace GF2Sparse.Degree1229\n\nopen Polynomial")
    print("\nset_option maxRecDepth 16384\nset_option maxHeartbeats 4000000\nset_option exponentiation.threshold 4096")
    print(f"\ndef knownPart : ℕ := {KNOWN}\ndef cofactor : ℕ := (2^1229-1) / knownPart")
    print(f"\nprivate abbrev modulus := productMask {N} {U} {V}")
    print("private noncomputable abbrev root := AdjoinRoot.root (decode modulus)")
    mask = (1 << N) | (1 << (U+V)) | (1 << V) | (1 << U) | 1
    for p, proof in prime_certificates(PRIMES).items():
        print(f"private def p{p} : ProvenPrime := {proof}")
    emit_modular_power(N, mask, 64, GROUP, "(2^1229-1)", "fullPower", full=True)
    for p in PRIMES:
        emit_modular_power(N, mask, 64, GROUP//p, f"(cofactor*(knownPart/{p}))", f"power{p}", full=False)
    emit_modular_power(N, mask, 64, KNOWN, "knownPart", "extraPower", full=False)
    print("""
theorem irreducible_candidate : Irreducible (productCandidate 1229 27 50) := by
  rw [← decode_productMask]
  have hdeg : (decode modulus).natDegree = 1229 := (natDegree_decode _).trans (by decide +kernel)
  apply irreducible_of_prime_degree_power (f := decode modulus) (by rw [hdeg]; norm_num)
  · intro x
    rw [decode_productMask]
    fin_cases x <;> simp only [productCandidate, eval_add, eval_pow, eval_X, eval_mul, eval_one] <;> decide +kernel
  · simpa only [hdeg] using fullPower

theorem order_split :
    ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧ orderOf (AdjoinRoot.root (productCandidate 1229 27 50)) = knownPart*t := by
  rw [← decode_productMask]
  have hnum : knownPart*cofactor = 2^1229-1 := by decide +kernel
  have hknown : orderOf (root^cofactor) = knownPart := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
    · rw [← pow_mul, Nat.mul_comm, hnum]; exact fullPower
    · intro q hq hdiv
      have hmem : q ∈ ([""" + ", ".join(str(p) for p in PRIMES) + """] : List ℕ) := by
        apply mem_list_primes_of_dvd_prod hq.prime _ (by simpa only [knownPart] using hdiv)
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with """ + " | ".join("rfl" for _ in PRIMES) + """
"""+ "\n".join(f"        · exact p{p}.property.prime" for p in PRIMES) + """
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rw [← pow_mul]
      rcases hmem with """ + " | ".join("rfl" for _ in PRIMES) + """
"""+ "\n".join(f"      · exact power{p}" for p in PRIMES) + """
  exact order_split_of_projection (by decide) (by decide +kernel) (hnum ▸ fullPower) hknown extraPower

end GF2Sparse.Degree1229""")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-lean", action="store_true")
    parser.add_argument("--bound", type=int, default=10**10)
    args = parser.parse_args()
    if args.bound <= 0:
        parser.error("the trial bound must be positive")
    if args.emit_lean:
        emit()
    else:
        check(args.bound)
