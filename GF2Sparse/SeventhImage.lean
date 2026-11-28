import GF2Sparse.CubicImage
import GF2Sparse.FrobeniusWitness
import Mathlib.Tactic.ReduceModChar

/-! Seventh powers linking two binary polynomials of weight at most five. -/

namespace GF2Sparse.SeventhImage
open Polynomial

def tail {R : Type*} [Semiring R] (t : R) : R := 1 + t^2 + t^3 + t^4

theorem tail_identity {R : Type*} [CommRing R] [CharP R 2] (t : R) :
    (tail t)^7 + t^28 + (t*(tail t)^2)^3 + (t*(tail t)^2)^2 + 1 = 0 := by
  unfold tail
  ring_nf
  reduce_mod_char!

noncomputable def source (n u : ℕ) : BinaryPoly := X^n + tail (X^u)

noncomputable def target (n u v : ℕ) : BinaryPoly :=
  X^n + (X^u)^4 + (X^v)^3 + (X^v)^2 + 1

theorem source_dvd_expand_target {n u v : ℕ} (hv : 7*v = u+n*2) :
    source n u ∣ expand (ZMod 2) 7 (target n u v) := by
  let f := source n u
  let m := AdjoinRoot.mk f
  have h : m (X^n) = m (tail (X^u)) := by
    apply sub_eq_zero.mp
    rw [← map_sub, CharTwo.sub_eq_add]
    exact AdjoinRoot.mk_self
  have hv' : ((X : BinaryPoly)^7)^v = X^u*(X^n)^2 := by
    simp only [← pow_mul, ← pow_add, hv]
  have hu : (((X : BinaryPoly)^7)^u)^4 = (X^u)^28 := by
    rw [pow_right_comm X 7 u, ← pow_mul]
  apply AdjoinRoot.mk_eq_zero.mp
  change m (expand (ZMod 2) 7 (target n u v)) = 0
  simp only [target, map_add, map_pow, map_one, expand_X, hv', hu, pow_right_comm X 7 n]
  simp only [map_mul, map_pow]
  have h' : m X ^ n = m (tail (X^u)) := by simpa only [map_pow] using h
  rw [h']
  simpa only [map_add, map_one, map_mul, map_pow, map_zero] using
    congrArg m (tail_identity ((X : BinaryPoly)^u))

private theorem degree_source {n u : ℕ} (hn : 4*u < n) : (source n u).natDegree = n := by
  have h : (tail ((X : BinaryPoly)^u)).natDegree ≤ 4*u := by
    unfold tail
    compute_degree
  unfold source
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  simpa only [natDegree_X_pow] using h.trans_lt hn

private theorem degree_target {n u v : ℕ} (hn : 4*u < n) (hv : 7*v = u+n*2) :
    (target n u v).natDegree = n := by
  unfold target
  rw [show (X^n + (X^u)^4 + (X^v)^3 + (X^v)^2 + 1 : BinaryPoly) =
    X^n + ((X^u)^4 + (X^v)^3 + (X^v)^2 + 1) by abel]
  have h : (((X^u)^4 + (X^v)^3 + (X^v)^2 + 1 : BinaryPoly)).natDegree ≤ n-1 := by
    compute_degree
    omega
  rw [natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  omega

theorem irreducible_target_iff {n u v : ℕ} (hn : 4*u < n) (hv : 7*v = u+n*2)
    (hc : (2^n-1).Coprime 7) : Irreducible (target n u v) ↔ Irreducible (source n u) :=
  irreducible_iff_of_coprime_sampling ((degree_source hn).trans (degree_target hn hv).symm)
    (source_dvd_expand_target hv) (by rwa [degree_source hn])

theorem target_root_order {n u v : ℕ} (hn : 4*u < n) (hv : 7*v = u+n*2)
    (hc : (2^n-1).Coprime 7) (hs : Irreducible (source n u)) :
    orderOf (AdjoinRoot.root (target n u v)) = orderOf (AdjoinRoot.root (source n u)) := by
  letI : Fact (Irreducible (source n u)) := ⟨hs⟩
  let r := AdjoinRoot.root (source n u)
  have hr : aeval r (source n u) = 0 := (AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self
  have h7 : aeval (r^7) (target n u v) = 0 := by
    rw [← expand_aeval, AdjoinRoot.aeval_eq]
    exact AdjoinRoot.mk_eq_zero.2 (source_dvd_expand_target hv)
  rw [← orderOf_root_at ((irreducible_target_iff hn hv hc).2 hs) h7]
  exact orderOf_pow_root_of_coprime hs hr (by decide) (by rwa [degree_source hn])

theorem primitive_target_iff {n u v : ℕ} (hn : 4*u < n) (hv : 7*v = u+n*2) :
    Primitive (target n u v) ↔ Primitive (source n u) ∧ (2^n-1).Coprime 7 := by
  have hs := degree_source hn
  have ht := degree_target hn hv
  have hsp : 0 < (source n u).natDegree := by omega
  have htp : 0 < (target n u v).natDegree := by omega
  simpa only [ht] using primitive_iff_of_dvd_expand (binary_monic (ne_zero_of_natDegree_gt htp))
    (binary_monic (ne_zero_of_natDegree_gt hsp)) htp (hs.trans ht.symm) (by decide : 0 < 7)
    (source_dvd_expand_target hv)

theorem primitive_pair_16 : Primitive (source 16 3) ∧ Primitive (target 16 3 5) := by
  let taps : List ℕ := [16,12,9,6,0]
  have he : decode (xorShifts taps 1) = source 16 3 := by
    simp only [taps, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
      pow_zero, mul_one, add_zero, source, tail]
    ring
  have hs : Primitive (source 16 3) := by
    rw [← he]
    exact (check_sound (n := 16) (factors := [3,5,17,257])
      (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl | rfl <;> norm_num)
      (by decide +kernel)).2.2
  exact ⟨hs, (primitive_target_iff (by decide) (by decide)).2 ⟨hs, by decide⟩⟩

end GF2Sparse.SeventhImage
