import GF2Sparse.OreMixedOrder

/-! Count two independently chosen multisets of generators at different
degree costs to bound the order of a root of an irreducible Ore lift. -/

namespace GF2Sparse

open Polynomial

private def joinMultisets {α β : Type*} (l : Multiset (Option α)) (r : Multiset β) :
    Multiset (Option (α ⊕ β)) :=
  l.map (Option.map Sum.inl) + r.map (fun j => some (Sum.inr j))

private theorem filter_nothing {α β : Type*} (s : Multiset α) :
    s.filterMap (fun _ => (none : Option β)) = 0 := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons i s ih => simp [ih]

private theorem joinMultisets_injective {α β : Type*} {u v : ℕ} :
    Function.Injective (fun z : Sym (Option α) u × Sym β v =>
      joinMultisets z.1.val z.2.val) := by
  let left : Option (α ⊕ β) → Option (Option α)
    | none => some none
    | some (.inl i) => some (some i)
    | some (.inr _) => none
  let right : Option (α ⊕ β) → Option β
    | some (.inr i) => some i
    | _ => none
  have left_id : left ∘ Option.map Sum.inl = some := by funext j; cases j <;> rfl
  have right_no : right ∘ Option.map Sum.inl = fun _ => none := by funext j; cases j <;> rfl
  have proj₁ (l : Multiset (Option α)) (r : Multiset β) : (joinMultisets l r).filterMap left = l := by
    rw [joinMultisets, Multiset.filterMap_add, Multiset.filterMap_map, Multiset.filterMap_map,
      left_id, Multiset.filterMap_some]
    change l + r.filterMap (fun _ => none) = l
    rw [filter_nothing, add_zero]
  have proj₂ (l : Multiset (Option α)) (r : Multiset β) : (joinMultisets l r).filterMap right = r := by
    rw [joinMultisets, Multiset.filterMap_add, Multiset.filterMap_map, Multiset.filterMap_map,
      right_no, filter_nothing, zero_add]
    exact Multiset.filterMap_some _
  intro z w h
  apply Prod.ext <;> apply Subtype.ext
  · simpa only [proj₁] using congrArg (Multiset.filterMap left) h
  · simpa only [proj₂] using congrArg (Multiset.filterMap right) h

private theorem sum_weights_le {α : Type*} (s : Multiset α) (f : α → ℕ) (d : ℕ)
    (h : ∀ j, f j ≤ d) : (s.map f).sum ≤ s.card*d := by
  have ht := Multiset.sum_le_card_nsmul (s.map f) d (by
    intro w hw; obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hw; exact h j)
  simpa using ht

/-- Use u factors from X and the positive-degree constant-one seeds of degree
at most a, and v factors from the seeds of degree exactly a+1. Both families
have 2^a members. -/
theorem Primitive.oreLift_order_two_layers {p : BinaryPoly} (hp : Primitive p)
    (a u v : ℕ) (ha : 0 < a) (hs : a+1 < p.natDegree)
    (hd : u*(2^a-1) + v*(2^(a+1)-1) < 2^p.natDegree-1) :
    (2^a+u-1).choose u * (2^a+v-1).choose v ≤ orderOf (AdjoinRoot.root (oreLift p)) := by
  let k := 2^a
  have hk : 1 < k := Nat.one_lt_two_pow ha.ne'
  let L := Fin (k-1)
  let R := Fin k
  let index : L ⊕ R → ℕ := Sum.elim (fun i => i.val+1) (fun i => k+i.val)
  have il (i : L) : i.val < k-1 := i.isLt
  have ir (i : R) : i.val < k := i.isLt
  have ii : Function.Injective index := by
    rintro (i|i) (j|j) h <;> simp only [index, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (Fin.ext (by omega))
    · have := il i; omega
    · have := il j; omega
    · exact congrArg Sum.inr (Fin.ext (by omega))
  let g (i : L ⊕ R) := decode (2*index i+1)
  have gi : Function.Injective g := by
    intro i j h
    have := decode_injective h
    apply ii
    omega
  have gc (i : L ⊕ R) : (g i).coeff 0 = 1 := by simp [g, Nat.testBit_zero]
  have gd (i : L ⊕ R) : 0 < (g i).natDegree := by
    change 1 ≤ (decode _).natDegree
    rw [natDegree_decode, Nat.le_log2 (by omega)]
    cases i <;> simp [index] <;> omega
  have gl (i : L) : (g (.inl i)).natDegree ≤ a := by
    apply Nat.lt_succ_iff.1
    rw [show (g (.inl i)).natDegree = (2*(i.val+1)+1).log2 from natDegree_decode _,
      Nat.log2_lt (by omega), pow_succ]
    change _ < k*2
    have := il i
    omega
  have gr (i : R) : (g (.inr i)).natDegree ≤ a+1 := by
    apply Nat.lt_succ_iff.1
    rw [show (g (.inr i)).natDegree = (2*(k+i.val)+1).log2 from natDegree_decode _,
      Nat.log2_lt (by omega), pow_succ, pow_succ]
    change _ < k*2*2
    have := ir i
    omega
  have hv (i : L ⊕ R) : ¬ p ∣ g i := by
    intro h
    have hl := natDegree_le_of_dvd h (fun e => by have := gc i; simp [e] at this)
    cases i with
    | inl j => have := gl j; omega
    | inr j => have := gr j; omega
  let wt (j : Option (L ⊕ R)) := j.elim 1 (fun i => 2^(g i).natDegree-1)
  have wl (j : Option L) : wt (Option.map Sum.inl j) ≤ k-1 := by
    cases j with
    | none => change 1 ≤ k-1; omega
    | some j =>
      have h := Nat.pow_le_pow_right (by decide : 0 < 2) (gl j)
      exact Nat.sub_le_sub_right h 1
  have wr (j : R) : wt (some (.inr j)) ≤ 2^(a+1)-1 :=
    Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide : 0 < 2) (gr j)) 1
  have bound := hp.oreLift_order_multisets g gi gc gd hv
    (fun z : Sym (Option L) u × Sym R v => joinMultisets z.1.val z.2.val) joinMultisets_injective (by
      intro z
      change ((joinMultisets _ _).map wt).sum < _
      rw [joinMultisets, Multiset.map_add, Multiset.sum_add, Multiset.map_map, Multiset.map_map]
      apply lt_of_le_of_lt (Nat.add_le_add (sum_weights_le _ _ _ wl) (sum_weights_le _ _ _ wr))
      simpa [z.1.property, z.2.property, k] using hd)
  have hcard : k-1+1=k := by omega
  simpa [Fintype.card_prod, Sym.card_sym_eq_choose, Fintype.card_option, L, R, hcard, k] using bound

end GF2Sparse
