"""Check the known and unresolved parts of the degree-1229 root order, or emit its Lean certificate."""

import argparse
import csv
from math import gcd, prod
from pathlib import Path

from flint import fmpz, nmod_poly

N, U, V = 1229, 27, 50
PRIMES = (36871, 46703, 10543179280661916121033, 9536289355314392579996071515160583098298616686033085857)
KNOWN = prod(PRIMES)
GROUP = (1 << N) - 1
COFACTOR, REMAINDER = divmod(GROUP, KNOWN)


def check_trinomials():
    from make_witnesses import remainder
    path = Path(__file__).resolve().parents[1] / "data" / "degree-1229-trinomial-factors.csv"
    checked = set()
    with path.open(newline="") as source:
        reader = csv.DictReader(source)
        if reader.fieldnames != ["tap", "factor_mask"]:
            raise ValueError("incorrect trinomial factor header")
        for expected, row in enumerate(reader, 1):
            a, g = int(row["tap"]), int(row["factor_mask"])
            if a != expected or a > N // 2 or g <= 1 or g % 2 == 0:
                raise ValueError(f"invalid tap or factor at row {expected}")
            reverse = int(f"{g:b}"[::-1], 2)
            for tap, factor in ((a, g), (N-a, reverse)):
                f = (1 << N) | (1 << tap) | 1
                if not 0 < factor.bit_length()-1 < N or remainder(f, factor):
                    raise ArithmeticError(f"failed proper factor at tap {tap}")
                checked.add(tap)
    if checked != set(range(1, N)):
        raise ArithmeticError("incomplete trinomial factor table")
    print(f"Verified a proper polynomial factor for all {len(checked)} trinomials of degree {N}.")


def check_known_order(f):
    if REMAINDER or gcd(KNOWN, COFACTOR) != 1 or not all(fmpz(p).is_prime() for p in PRIMES):
        raise ValueError("incorrect known factors")
    if fmpz(COFACTOR).is_prime():
        raise ValueError("the unresolved factor is prime")
    x = nmod_poly([0, 1], 2)
    if x.pow_mod(GROUP, f) != 1:
        raise ValueError("the root fails the field-order test")
    for d in PRIMES:
        if x.pow_mod(GROUP//d, f) == 1:
            raise ValueError(f"the root order misses the known prime {d}")
    if x.pow_mod(KNOWN, f) == 1:
        raise ValueError("the root order divides the known part")


def check(bound, taps=(U, V, U+V)):
    x = nmod_poly([0, 1], 2)
    f = x**N + sum((x**i for i in taps), x**0)
    check_known_order(f)
    for candidate in range(2*N+1, bound+1, 2*N):
        if COFACTOR % candidate == 0:
            raise ValueError(f"found a new divisor {candidate}")
    print(f"The unresolved cofactor is {COFACTOR}.")
    print(f"The root order is {KNOWN} times a divisor of the {len(str(COFACTOR))}-digit cofactor.")
    print(f"Every prime of that cofactor exceeds {bound}. The root order exceeds 2^{(KNOWN*bound).bit_length()-1}.")


def emit():
    from make_witnesses import emit_modular_power, prime_certificates
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

theorem order_split_of_powers {G : Type*} [Monoid G] (r : G)
    (full : r^(2^1229-1) = 1) (extra : r^knownPart ≠ 1)
    (proper : ∀ p ∈ ([""" + ", ".join(str(p) for p in PRIMES) + """] : List ℕ),
      r^(cofactor*(knownPart/p)) ≠ 1) :
    ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧ orderOf r = knownPart*t := by
  have hnum : knownPart*cofactor = 2^1229-1 := by decide +kernel
  have hknown : orderOf (r^cofactor) = knownPart := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
    · rw [← pow_mul, Nat.mul_comm, hnum]; exact full
    · intro q hq hdiv
      have hmem : q ∈ ([""" + ", ".join(str(p) for p in PRIMES) + """] : List ℕ) := by
        apply mem_list_primes_of_dvd_prod hq.prime _ (by simpa only [knownPart] using hdiv)
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with """ + " | ".join("rfl" for _ in PRIMES) + """
"""+ "\n".join(f"        · exact p{p}.property.prime" for p in PRIMES) + """
      rw [← pow_mul]
      exact proper q hmem
  exact order_split_of_projection (by decide) (by decide +kernel) (hnum ▸ full) hknown extra

theorem order_split :
    ∃ t : ℕ, 1 < t ∧ t ∣ cofactor ∧ orderOf (AdjoinRoot.root (productCandidate 1229 27 50)) = knownPart*t := by
  rw [← decode_productMask]
  apply order_split_of_powers root fullPower extraPower
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with """ + " | ".join("rfl" for _ in PRIMES) + """
"""+ "\n".join(f"  · exact power{p}" for p in PRIMES) + """

end GF2Sparse.Degree1229""")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--emit-lean", action="store_true")
    action.add_argument("--seroussi", action="store_true", help="check the published taps 2, 6, 15")
    action.add_argument("--trinomials", action="store_true", help="verify the complete trinomial exclusion")
    parser.add_argument("--bound", type=int, default=10**10)
    args = parser.parse_args()
    if args.bound <= 0:
        parser.error("the trial bound must be positive")
    if args.emit_lean:
        emit()
    elif args.trinomials:
        check_trinomials()
    else:
        check(args.bound, (2, 6, 15) if args.seroussi else (U, V, U+V))
