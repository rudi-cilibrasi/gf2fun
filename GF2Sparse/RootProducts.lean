import GF2Sparse.TripleRoots
import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
import Mathlib.Data.Multiset.Replicate

/-! Products of at most k distinct binary roots are the pointwise k-th power
of the entire root set. This permits testing several ranks with one gcd. -/

namespace GF2Sparse

open scoped Pointwise
open Polynomial

variable {M : Type*} [CommMonoid M]

private theorem compress_product (S : Set M) (hs : ∀ a ∈ S, a*a ∈ S)
    (p : Multiset M) (hn : 0 < p.card) (hp : ∀ x ∈ p, x ∈ S) :
    ∃ q : Finset M, q.Nonempty ∧ (∀ x ∈ q, x ∈ S) ∧ q.card ≤ p.card ∧ ∏ x ∈ q, x = p.prod := by
  classical
  by_cases hd : p.Nodup
  · exact ⟨⟨p, hd⟩, Finset.card_pos.1 hn, hp, le_rfl, by simp [Finset.prod_mk]⟩
  rw [Multiset.nodup_iff_ne_cons_cons] at hd
  push Not at hd
  obtain ⟨a, r, rfl⟩ := hd
  have ha := hp a (by simp)
  have hnew : ∀ x ∈ (a*a) ::ₘ r, x ∈ S := by
    intro x hx
    rcases Multiset.mem_cons.1 hx with rfl | hx
    · exact hs a ha
    · exact hp x (by simp [hx])
  obtain ⟨q, hq, hm, hc, he⟩ := compress_product S hs ((a*a) ::ₘ r) (by simp) hnew
  exact ⟨q, hq, hm, hc.trans (by simp), by simpa [mul_assoc] using he⟩
termination_by p.card
decreasing_by simp_all

private theorem finset_prod_mem_pow {S : Set M} (q : Finset M)
    (hq : ∀ x ∈ q, x ∈ S) : (∏ x ∈ q, x) ∈ S ^ q.card := by
  classical
  induction q using Finset.induction_on with
  | empty => simp
  | insert x q hx ih =>
    rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx, pow_succ']
    exact Set.mul_mem_mul (hq x (by simp)) (ih (fun z hz => hq z (by simp [hz])))

/-- If squaring maps a set onto itself, its k-fold product set represents
exactly the nonempty distinct selections of size at most k. -/
theorem mem_pow_iff_short_product (S : Set M) (hs : ∀ a ∈ S, a*a ∈ S)
    (hr : ∀ a ∈ S, ∃ b ∈ S, b*b = a) {n : ℕ} (hn : 0 < n) (a : M) :
    a ∈ S ^ n ↔ ∃ q : Finset M, q.Nonempty ∧ (∀ x ∈ q, x ∈ S) ∧ q.card ≤ n ∧ ∏ x ∈ q, x = a := by
  constructor
  · intro h
    obtain ⟨f, hf, he⟩ := Set.mem_pow_iff_prod.1 h
    let p := Finset.univ.val.map f
    have hc : p.card = n := by simp [p]
    have hp : ∀ x ∈ p, x ∈ S := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.1 hx
      exact hf i
    have he' : p.prod = a := he
    simpa only [hc, he'] using compress_product S hs p (hc ▸ hn) hp
  · rintro ⟨q, hq, hm, hc, rfl⟩
    have hsub : S ⊆ S * S := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hr x hx
      exact Set.mul_mem_mul hy hy
    have hmono : Monotone (fun k : ℕ => S ^ (k+1)) := by
      apply monotone_nat_of_le_succ
      intro k
      calc
        S ^ (k+1) = S ^ k * S := pow_succ _ _
        _ ⊆ S ^ k * (S * S) := Set.mul_subset_mul_left hsub
        _ = S ^ (k+1+1) := by rw [← mul_assoc, ← pow_succ, ← pow_succ]
    have hp := finset_prod_mem_pow q hm
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hq.card_pos.ne'
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [hk] at hp hc
    rw [hj] at hc ⊢
    exact hmono (by omega : k ≤ j) hp

/-- The finite selections in the exterior-power test of a squarefree binary
polynomial can be checked using ordinary products with repetitions. -/
theorem binary_root_products (f : BinaryPoly) {n : ℕ} (hn : 0 < n)
    (a : AlgebraicClosure (ZMod 2)) :
    let S := {x : AlgebraicClosure (ZMod 2) | aeval x f = 0}
    a ∈ S ^ n ↔ ∃ q : Finset (AlgebraicClosure (ZMod 2)), q.Nonempty ∧
      (∀ x ∈ q, aeval x f = 0) ∧ q.card ≤ n ∧ ∏ x ∈ q, x = a := by
  apply mem_pow_iff_short_product _ _ _ hn
  · intro x hx
    change aeval x f = 0 at hx
    change aeval (x*x) f = 0
    rw [← pow_two]
    change aeval (x ^ (2 ^ 1)) f = 0
    rw [aeval_dyadic, hx]
    simp
  · intro x hx
    change aeval x f = 0 at hx
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x (zero_lt_two' ℕ)
    refine ⟨y, ?_, by rwa [← pow_two]⟩
    change aeval y f = 0
    rw [← hy] at hx
    change aeval (y ^ (2 ^ 1)) f = 0 at hx
    rw [aeval_dyadic] at hx
    exact eq_zero_of_pow_eq_zero hx

/-- The n-th powers distinguish representatives of distinct orbits under a generator of order n. -/
theorem injective_cyclic_orbits_of_power {G ι : Type*} [CommGroup G]
    (g : G) (s : ι → G) (hs : Function.Injective (fun i => (s i) ^ orderOf g)) :
    Function.Injective (fun u : ι × Fin (orderOf g) => s u.1 * g ^ (u.2 : ℕ)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  change s i * g ^ (j : ℕ) = s i' * g ^ (j' : ℕ) at h
  have fixed (k : ℕ) : (g ^ k) ^ orderOf g = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hi : i = i' := hs (by
    simpa only [mul_pow, fixed, mul_one] using congrArg (fun x : G => x ^ orderOf g) h)
  subst i'
  have hj : j = j' := Fin.ext (pow_injOn_Iio_orderOf j.isLt j'.isLt (mul_left_cancel h))
  cases hj
  rfl

/-- Distinct dyadic exponent sums modulo an order divisor give distinct products of conjugates. -/
theorem injective_conjugate_products_of_exponent_sums
    (r : M) (hr : IsOfFinOrder r) {p : ℕ} (hp : p ∣ orderOf r) (S : Set (Finset ℕ))
    (hs : S.InjOn (fun I => (∑ i ∈ I, 2 ^ i : ℕ) % p)) :
    S.InjOn (fun I => ∏ i ∈ I, r ^ (2 ^ i : ℕ)) := by
  intro I hI J hJ h
  change (∏ i ∈ I, r ^ (2 ^ i : ℕ)) = ∏ j ∈ J, r ^ (2 ^ j : ℕ) at h
  rw [Finset.prod_pow_eq_pow_sum I (fun i => 2 ^ i) r,
      Finset.prod_pow_eq_pow_sum J (fun j => 2 ^ j) r] at h
  exact hs hI hJ (Nat.ModEq.of_dvd hp (hr.pow_eq_pow_iff_modEq.mp h))

end GF2Sparse
