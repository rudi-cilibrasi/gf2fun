import GF2Sparse.OreLift

/-! An equivalent all-degree conjecture stated solely in terms of sparse irreducibles. -/

namespace GF2Sparse

open Polynomial

theorem mem_range_oreLift_iff (f : BinaryPoly) :
    f ∈ Set.range oreLift ↔ (f.support : Set ℕ) ⊆ Set.range oreIndex := by
  change _ ↔ (f.toFinsupp.support : Set ℕ) ⊆ Set.range oreIndex
  rw [← Finsupp.mem_range_embDomain_iff]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.toFinsupp, rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨⟨v⟩, toFinsupp_injective hv⟩

/-- A constant-one irreducible in degree 2^s-1 whose at most five exponents
all have the form 2^i-1. -/
def HasSparseOreIrreducible (s : ℕ) : Prop :=
  ∃ f : BinaryPoly, f.natDegree = 2^s-1 ∧ f.support.card ≤ 5 ∧
    (f.support : Set ℕ) ⊆ Set.range oreIndex ∧ f.coeff 0 = 1 ∧ Irreducible f

theorem sparsePrimitive_iff_sparseOreIrreducible {s : ℕ} (hs : 0 < s) :
    HasSparsePrimitive s ↔ HasSparseOreIrreducible s := by
  constructor
  · rintro ⟨p, rfl, hw, hp⟩
    exact ⟨oreLift p, oreLift_degree hp.2.1.ne_zero, (oreLift_weight p).trans_le hw,
      (mem_range_oreLift_iff _).1 ⟨p, rfl⟩, (oreLift_constant p).trans hp.coeff_zero_eq_one,
      hp.irreducible_oreLift⟩
  · rintro ⟨f, hd, hw, hsup, hc, hf⟩
    obtain ⟨p, rfl⟩ := (mem_range_oreLift_iff f).2 hsup
    have hc' : p.coeff 0 = 1 := by simpa using hc
    have hp : p ≠ 0 := by intro he; simp [he] at hc'
    have hs' : p.natDegree = s := oreIndex.injective ((oreLift_degree hp).symm.trans hd)
    exact ⟨p, hs', by simpa using hw, (irreducible_oreLift_iff (hs' ▸ hs) hc').1 hf⟩

theorem conjecture_iff_sparseOreIrreducible :
    Conjecture ↔ ∀ s : ℕ, 0 < s → HasSparseOreIrreducible s :=
  ⟨fun h s hs => (sparsePrimitive_iff_sparseOreIrreducible hs).1 (h s hs),
    fun h s hs => (sparsePrimitive_iff_sparseOreIrreducible hs).2 (h s hs)⟩

end GF2Sparse
