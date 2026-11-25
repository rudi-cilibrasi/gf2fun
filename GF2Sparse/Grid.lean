import GF2Sparse.LocalFactors

/-! Obstructions to choosing the exponents within bounded distance of a
fixed set of rational multiples of the degree. -/

namespace GF2Sparse

open Polynomial

private def exponent {ι : Type*} (n : ℕ) (e : ι → ℕ) : Option (Option ι) → ℕ
  | none => n
  | some none => 0
  | some (some i) => e i

/-- Keep the two endpoints and compress all interior exponents to the open
interval (0,m), preserving their residues. The resulting degree-m polynomial
supplies a factor of the original one. -/
theorem factor_of_compressed_interior {ι : Type*} [Fintype ι] {m n : ℕ}
    (hm : 0 < m) (a b : ι → ℕ) (hb : ∀ i, 0 < b i ∧ b i < m)
    (hend : n ≡ m [MOD period m]) (hint : ∀ i, a i ≡ b i [MOD period m]) :
    ∃ p : BinaryPoly, Irreducible p ∧ p.natDegree ≤ m ∧
      p ∣ X ^ n + (1 + ∑ i, X ^ a i) := by
  classical
  let t : BinaryPoly := ∑ i, X ^ b i
  let g : BinaryPoly := X ^ m + (1 + t)
  have ht : t.natDegree < m := by
    apply Nat.lt_of_le_of_lt ((natDegree_le_iff_coeff_eq_zero (n := m - 1)).2 ?_) (by omega)
    intro j hj
    have hz (i) : j ≠ b i := by have := (hb i).2; omega
    simp [t, coeff_X_pow, hz]
  have hgdeg : g.natDegree = m := by
    apply (natDegree_add_eq_left_of_natDegree_lt _).trans (natDegree_X_pow m)
    rw [natDegree_X_pow]
    exact (natDegree_add_le 1 t).trans_lt (max_lt (by simpa using hm) ht)
  have hconst : g.coeff 0 = 1 := by
    simp [g, t, coeff_X_pow, hm.ne, fun i => (hb i).1.ne]
  have heq : g = ∑ i, X ^ exponent m b i := by simp [g, t, Fintype.sum_option, exponent]
  have hmod (i : Option (Option ι)) : exponent n a i ≡ exponent m b i [MOD period m] := by
    rcases i with _ | (_ | i)
    · exact hend
    · rfl
    · exact hint i
  have h := factor_of_congruent_exponents Finset.univ (exponent n a) (exponent m b)
    (fun i _ => hmod i) g heq (hgdeg ▸ hm) hgdeg.le hconst
  simpa [Fintype.sum_option, exponent] using h

private theorem compress_offset {D M w L shift e j : ℕ} (hM : w < M)
    (he0 : 0 < e) (he : e < D * (M + L * shift)) (hj : j ≤ D)
    (hlo : j * (M + L * shift) ≤ e + w) (hhi : e ≤ j * (M + L * shift) + w) :
    ∃ b : ℕ, (0 < b ∧ b < D * M) ∧ e ≡ b [MOD L] := by
  simp only [Nat.mul_add] at he hlo hhi
  have hstart : j * (L * shift) < e := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · simpa using he0
    · have hh : M ≤ j * M := by simpa using Nat.mul_le_mul_right M h
      omega
  have hstop : e < D * M + j * (L * shift) := by
    rcases hj.eq_or_lt with rfl | h
    · exact he
    · have hh := Nat.mul_le_mul_right M h
      rw [Nat.succ_mul] at hh
      omega
  refine ⟨e - j * (L * shift), ⟨by omega, by omega⟩, ?_⟩
  symm
  apply (Nat.modEq_iff_dvd' (Nat.sub_le e _)).2
  rw [Nat.sub_sub_self hstart.le]
  exact dvd_mul_of_dvd_right (dvd_mul_right L shift) j

/-- Fix a grid with D equal intervals and allow an error of w at every grid
point. On a whole progression of degrees, all polynomials supported there,
with both endpoints present, have an irreducible factor of degree at most D*M.
Taking k > 0 makes this factor proper. -/
theorem rational_grid_factor {ι : Type*} [Fintype ι] (D M w k : ℕ) (hD : 0 < D) (hw : w < M)
    (a : ι → ℕ) (ha : ∀ i, 0 < a i ∧ a i < D * (M + period (D * M) * k))
    (hgrid : ∀ i, ∃ j ≤ D, j * (M + period (D * M) * k) ≤ a i + w ∧
      a i ≤ j * (M + period (D * M) * k) + w) :
    ∃ p : BinaryPoly, Irreducible p ∧ p.natDegree ≤ D * M ∧
      p ∣ X ^ (D * (M + period (D * M) * k)) + (1 + ∑ i, X ^ a i) := by
  have h (i : ι) : ∃ b : ℕ, (0 < b ∧ b < D * M) ∧ a i ≡ b [MOD period (D * M)] := by
    obtain ⟨j, hj, hlo, hhi⟩ := hgrid i
    exact compress_offset hw (ha i).1 (ha i).2 hj hlo hhi
  choose b hb hmod using h
  apply factor_of_compressed_interior (Nat.mul_pos hD (by omega)) a b hb _ hmod
  rw [Nat.mul_add, Nat.add_comm, Nat.mul_left_comm]
  exact Nat.ModEq.modulus_mul_add

end GF2Sparse
