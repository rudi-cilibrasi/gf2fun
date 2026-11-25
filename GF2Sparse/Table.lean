import GF2Sparse.Certificate
import GF2Sparse.LocalFactors
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

/-! Finite tables with a proof of primality for every supplied integer factor. -/

namespace GF2Sparse

open Polynomial

abbrev ProvenPrime := {p : ℕ // p.Prime}

private theorem binPow_eq_pow {M : Type*} [Monoid M] (e : ℕ) (a : M) :
    npowBinRec e a = a ^ e := by
  induction e with
  | zero => simp [npowBinRec_zero]
  | succ e ih => rw [npowBinRec_succ, ih, pow_succ]

private def lucasCheck (p a : ℕ) (factors : List ProvenPrime) : Bool :=
  let power (k : ℕ) := npowBinRec k (a : ZMod p)
  (factors.map Subtype.val).prod == p - 1 && power (p - 1) == 1 &&
    factors.all (fun q => power ((p - 1) / q.val) != 1)

/-- A Lucas certificate can reuse the proven primes appearing in other rows. -/
def lucasPrime (p a : ℕ) (factors : List ProvenPrime)
    (h : lucasCheck p a factors = true) : ProvenPrime := by
  simp only [lucasCheck, binPow_eq_pow, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    List.all_eq_true] at h
  refine ⟨p, lucas_primality p (a : ZMod p) h.1.2 ?_⟩
  intro q hq hdvd
  have hprimes : ∀ z ∈ factors.map Subtype.val, Prime z := by
    intro z hz
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hz
    exact c.property.prime
  have hmem := mem_list_primes_of_dvd_prod hq.prime hprimes (h.1.1.symm ▸ hdvd)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hmem
  exact h.2 c hc

abbrev Row := ℕ × List ProvenPrime

def checkRows : ℕ → List Row → Bool
  | _, [] => true
  | start, (f, primes) :: rows =>
    check start f (primes.map Subtype.val) && checkRows (start + 1) rows

theorem checkRows_sound (rows : List Row) (start : ℕ) (h : checkRows start rows = true)
    (n : ℕ) (hlo : start ≤ n) (hhi : n < start + rows.length) : HasSparsePrimitive n := by
  induction rows generalizing start with
  | nil => simp at hhi; omega
  | cons row rows ih =>
    rcases row with ⟨f, primes⟩
    obtain ⟨hhead, htail⟩ := Bool.and_eq_true_iff.1 h
    rcases hlo.eq_or_lt with rfl | hlt
    · refine ⟨decode f, check_sound ?_ hhead⟩
      intro p hp
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hp
      exact c.property
    · apply ih (start + 1) htail hlt
      simp only [List.length_cons] at hhi
      omega

/-- A version of the conjecture with two free interior exponents. The third
is their sum. -/
def HasPrimitiveProduct (n : ℕ) : Prop :=
  ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ u ≠ v ∧ u + v < n ∧ Primitive (productCandidate n u v)

theorem HasPrimitiveProduct.sparse {n : ℕ} (h : HasPrimitiveProduct n) : HasSparsePrimitive n := by
  obtain ⟨u, v, hu, hv, huv, htop, hp⟩ := h
  have hs := product_shape hu hv huv htop
  exact ⟨_, hs.1, hs.2.le, hp⟩

def productMask (n u v : ℕ) := 2 ^ n ^^^ 2 ^ (u + v) ^^^ 2 ^ u ^^^ 2 ^ v ^^^ 1

theorem decode_pow_two (k : ℕ) : decode (2 ^ k) = X ^ k := by
  ext i
  simp [Nat.testBit_two_pow, coeff_X_pow, eq_comm]

def fiveTermMask (n c b a : ℕ) : ℕ := 2 ^ n ^^^ 2 ^ c ^^^ 2 ^ b ^^^ 2 ^ a ^^^ 1

theorem decode_fiveTermMask (n c b a : ℕ) :
    decode (fiveTermMask n c b a) = X ^ n + X ^ c + X ^ b + X ^ a + 1 := by
  simp only [fiveTermMask, decode_xor, decode_pow_two, decode_one]

theorem certify_five_terms (n c b a : ℕ) (ps : List ℕ)
    (hp : ∀ p ∈ ps, Nat.Prime p) (h : check n (fiveTermMask n c b a) ps = true) :
    Primitive (X ^ n + X ^ c + X ^ b + X ^ a + 1) := by
  rw [← decode_fiveTermMask]
  exact (check_sound hp h).2.2

theorem decode_productMask (n u v : ℕ) : decode (productMask n u v) = productCandidate n u v := by
  simp only [productMask, decode_xor, decode_pow_two, decode_one, productCandidate]
  rw [pow_add]
  ring

def productEntry (n u v : ℕ) (primes : List ProvenPrime)
    (h : check n (productMask n u v) (primes.map Subtype.val) = true)
    (hshape : 0 < u ∧ 0 < v ∧ u ≠ v ∧ u + v < n := by decide) :
    {k : ℕ // HasPrimitiveProduct k} := ⟨n, by
  obtain ⟨hu, hv, huv, htop⟩ := hshape
  refine ⟨u, v, hu, hv, huv, htop, ?_⟩
  rw [← decode_productMask]
  refine (check_sound ?_ h).2.2
  intro p hp
  obtain ⟨c, _, rfl⟩ := List.mem_map.1 hp
  exact c.property⟩

theorem covers_range {P : ℕ → Prop} (rows : List {k : ℕ // P k}) (start len : ℕ)
    (h : rows.map Subtype.val = List.range' start len) (n : ℕ) (hlo : start ≤ n)
    (hhi : n < start + len) : P n := by
  have hm : n ∈ rows.map Subtype.val := h ▸ (List.mem_range'_1.2 ⟨hlo, hhi⟩)
  obtain ⟨c, _, rfl⟩ := List.mem_map.1 hm
  exact c.property

/-- Each prime divisor may carry a separate proof for its proper power.
This allows large exponentiations to be replayed one at a time. -/
theorem primitive_of_certified_powers {n f : ℕ} (hn : 0 < n) (hd : f.log2 = n)
    (hfull : AdjoinRoot.root (decode f) ^ (2 ^ n - 1) = 1)
    (factors : List {p : ProvenPrime //
      AdjoinRoot.root (decode f) ^ ((2 ^ n - 1) / p.val) ≠ 1})
    (hprod : (factors.map (fun c => c.val.val)).prod = 2 ^ n - 1) : Primitive (decode f) := by
  have hf : f ≠ 0 := by rintro rfl; simp at hd; omega
  have hdeg := (natDegree_decode f).trans hd
  apply primitive_of_prime_checks (monic_decode hf) (hdeg ▸ hn)
  · rwa [hdeg]
  · rw [hdeg]
    intro p hp hdvd
    have hall : ∀ q ∈ factors.map (fun c => c.val.val), Prime q := by
      intro q hq
      obtain ⟨c, _, rfl⟩ := List.mem_map.1 hq
      exact c.val.property.prime
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 (mem_list_primes_of_dvd_prod hp.prime hall (hprod.symm ▸ hdvd))
    exact c.property

end GF2Sparse
