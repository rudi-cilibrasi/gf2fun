import GF2Sparse.OreSubsetProducts
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-! The common-scalar and integer-order steps used to separate components
of the order of an Ore root. -/

namespace GF2Sparse

/-- Impose a family of binary coordinate conditions simultaneously on all
the scaled inputs. The kernel contains a nonzero scalar if there are fewer
possible coordinate tuples than scalars. -/
theorem exists_common_binary_scale {E ι δ : Type*} [Field E] [Fintype E] [Fintype ι] [Fintype δ]
    (a : ι → E) (coord : δ → E →+ ZMod 2)
    (h : 2^(Fintype.card ι * Fintype.card δ) < Fintype.card E) :
    ∃ c : E, c ≠ 0 ∧ ∀ i j, coord j (c*a i) = 0 := by
  classical
  let T (x : E) (ij : ι × δ) := coord ij.2 (x*a ij.1)
  have hcard : Fintype.card (ι × δ → ZMod 2) < Fintype.card E := by
    simpa only [Fintype.card_fun, Fintype.card_prod, ZMod.card] using h
  obtain ⟨x,y,hne,he⟩ := Fintype.exists_ne_map_eq_of_card_lt T hcard
  refine ⟨x-y,sub_ne_zero.2 hne,fun i j => ?_⟩
  rw [sub_mul, map_sub, sub_eq_zero]
  exact congrFun he (i,j)

private theorem two_order_dvd_iff (m k : ℕ) :
    orderOf (2 : ZMod m) ∣ k ↔ m ∣ 2^k-1 := by
  calc
    _ ↔ (1 : ZMod m) = ((2^k : ℕ) : ZMod m) := by simp [orderOf_dvd_iff_pow_eq_one, eq_comm]
    _ ↔ m ∣ 2^k-1 := by
      simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff 1 (2^k) m).trans
        (Nat.modEq_iff_dvd' (Nat.two_pow_pos k))

/-- An order which does not divide a product of proper-subfield group sizes
has a prime-power divisor whose order of 2 avoids every selected degree. -/
theorem exists_prime_power_avoiding_subfields {ι : Type*} (ds : ι → ℕ) (I : Finset ι)
    {n h : ℕ} (hh : h ∣ 2^n-1) (havoid : ¬ h ∣ ∏ i ∈ I, (2^(ds i)-1)) :
    ∃ q e : ℕ, q.Prime ∧ 0 < e ∧ q^e ∣ h ∧ orderOf (2 : ZMod (q^e)) ∣ n ∧
      ∀ i ∈ I, ¬ orderOf (2 : ZMod (q^e)) ∣ ds i := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd] at havoid
  push Not at havoid
  obtain ⟨q,e,hq,hdiv,hmiss⟩ := havoid
  have he : 0 < e := by
    by_contra! hz
    have : e = 0 := by omega
    simp [this] at hmiss
  refine ⟨q,e,hq,he,hdiv,(two_order_dvd_iff _ _).2 (hdiv.trans hh),fun i hi h => ?_⟩
  exact hmiss (((two_order_dvd_iff _ _).1 h).trans (Finset.dvd_prod_of_mem _ hi))

/-- Taking all maximal proper subfield degrees forces one prime power
with the full order n of 2. -/
theorem exists_prime_power_full_degree {n h : ℕ} (hn : 0 < n) (hh : h ∣ 2^n-1)
    (havoid : ¬ h ∣ ∏ p ∈ n.primeFactors, (2^(n/p)-1)) :
    ∃ q e : ℕ, q.Prime ∧ 0 < e ∧ q^e ∣ h ∧ orderOf (2 : ZMod (q^e)) = n := by
  obtain ⟨q,e,hq,he,hdiv,ho,hskip⟩ :=
    exists_prime_power_avoiding_subfields (fun p => n/p) n.primeFactors hh havoid
  refine ⟨q,e,hq,he,hdiv,?_⟩
  let o := orderOf (2 : ZMod (q^e))
  change o = n
  obtain ⟨m,hm⟩ : o ∣ n := ho
  by_contra hne
  have hm1 : m ≠ 1 := fun eq => hne (by simpa [eq] using hm.symm)
  obtain ⟨p,hp,u,hu⟩ := Nat.exists_prime_and_dvd hm1
  have hn' : n = (o*u)*p := by rw [hm, hu]; ac_rfl
  have pd : p ∣ n := hn' ▸ dvd_mul_left p (o*u)
  apply hskip p (Nat.mem_primeFactors.2 ⟨hp,pd,hn.ne'⟩)
  show o ∣ n/p
  rw [Nat.div_eq_of_eq_mul_left hp.pos hn']
  exact dvd_mul_right _ _

end GF2Sparse
