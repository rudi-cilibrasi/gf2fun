import GF2Sparse.OreLift
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Central

/-! An element with a prescribed Frobenius annihilator distinguishes each
same-degree linearized generator in the multiplicative subgroup of a lifted root. -/

namespace GF2Sparse

open Polynomial FiniteField

private abbrev K := AlgebraicClosure (ZMod 2)
private noncomputable abbrev F := (frobeniusAlgHom (ZMod 2) K).toLinearMap
private noncomputable abbrev act (p : BinaryPoly) := aeval F p

private theorem act_mul (a b : BinaryPoly) (x : K) : act (a*b) x = act a (act b x) := by
  simp only [act, map_mul, Module.End.mul_apply]

private theorem act_comm (a b : BinaryPoly) (x : K) : act a (act b x) = act b (act a x) := by
  rw [← act_mul, mul_comm, act_mul]

private theorem act_surjective {p : BinaryPoly} (hp : p ≠ 0) : Function.Surjective (act p) := by
  let L : BinaryPoly := X * oreLift p
  have hq := oreLift_ne_zero hp
  have hd : 0 < L.natDegree := by rw [show L = _ from rfl, natDegree_mul X_ne_zero hq, natDegree_X]; omega
  have hs := IsAlgClosed.eval_surjective (p := L.map (algebraMap (ZMod 2) K))
    (by rw [natDegree_map]; exact hd.ne')
  intro y
  obtain ⟨x, hx⟩ := hs y
  refine ⟨x, ?_⟩
  change (L.map _).eval x = y at hx
  simpa [L, act, oreLift_frobenius, eval_map_algebraMap] using hx

/-- A nonzero root of the linearized polynomial of an irreducible q
has annihilator ideal (q) under the action of binary Frobenius. -/
private theorem irreducible_annihilator {q : BinaryPoly} (hq : Irreducible q) {z : K}
    (hz : z ≠ 0) (hkill : act q z = 0) (a : BinaryPoly) : act a z = 0 ↔ q ∣ a := by
  constructor
  · intro ha
    exact hq.dvd_iff_not_isCoprime.2 fun h =>
      hz (Submodule.disjoint_def.1 (disjoint_ker_aeval_of_isCoprime F h) z hkill ha)
  · rintro ⟨u, rfl⟩
    rw [mul_comm, act_mul, hkill, map_zero]

/-- Every constant-one binary polynomial is the exact annihilator of a
point of the algebraic closure when Y acts by squaring. -/
theorem exists_exact_frobenius_annihilator (g : BinaryPoly) (hc : g.coeff 0 = 1) :
    ∃ z : K, ∀ a : BinaryPoly, aeval F a z = 0 ↔ g ∣ a := by
  classical
  have hg : g ≠ 0 := by intro e; simp [e] at hc
  by_cases hd : 0 < g.natDegree
  · obtain ⟨q, hq, hqg⟩ := WfDvdMonoid.exists_irreducible_factor (not_isUnit_of_natDegree_pos g hd) hg
    obtain ⟨b, hb⟩ := hqg
    have hb0 : b ≠ 0 := by rintro rfl; simp [hb] at hg
    have hconst := hc
    rw [hb, mul_coeff_zero] at hconst
    have bit : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    have hqc : q.coeff 0 = 1 := bit _ (by intro e; simp [e] at hconst)
    have hbc : b.coeff 0 = 1 := bit _ (by intro e; simp [e] at hconst)
    have hlt : b.natDegree < g.natDegree := by
      rw [hb, natDegree_mul hq.ne_zero hb0]; have := hq.natDegree_pos; omega
    obtain ⟨y, hy⟩ := exists_exact_frobenius_annihilator b hbc
    obtain ⟨v, hv⟩ := act_surjective hq.ne_zero y
    have hyb := (hy b).2 dvd_rfl
    have pick : ∃ z : K, act q z = y ∧ act b z ≠ 0 := by
      by_cases hvb : act b v = 0
      · have hnd : ¬ q ∣ b := by
          rintro ⟨t, ht⟩
          have ht0 : t ≠ 0 := by rintro rfl; simp [ht] at hb0
          have hk : act t y = 0 := by rw [← hv, ← act_mul, mul_comm, ← ht, hvb]
          have hl := natDegree_le_of_dvd ((hy t).1 hk) ht0
          rw [ht, natDegree_mul hq.ne_zero ht0] at hl
          have := hq.natDegree_pos
          omega
        have hpos : 0 < (oreLift q).natDegree := by
          rw [oreLift_degree hq.ne_zero]; exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow hq.natDegree_pos.ne')
        obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero K (oreLift q) (degree_ne_of_natDegree_ne hpos.ne')
        have hw0 : w ≠ 0 := by rintro rfl; rw [← coeff_zero_eq_aeval_zero', oreLift_constant, hqc, map_one] at hw; exact one_ne_zero hw
        have hwq : act q w = 0 := by rw [oreLift_frobenius, hw, mul_zero]
        exact ⟨v+w, by rw [map_add, hv, hwq, add_zero], by
          rw [map_add, hvb, zero_add]; exact fun h => hnd ((irreducible_annihilator hq hw0 hwq b).1 h)⟩
      · exact ⟨v, hv, hvb⟩
    obtain ⟨z, hqz, hbz⟩ := pick
    have hq' : act q (act b z) = 0 := by rw [act_comm, hqz]; exact hyb
    refine ⟨z, fun a => ⟨fun ha => ?_, ?_⟩⟩
    · have hay : act a y = 0 := by rw [← hqz, act_comm, ha, map_zero]
      obtain ⟨u, hu⟩ := (hy a).1 hay
      have hu' : act u (act b z) = 0 := by rw [← act_mul, mul_comm, ← hu]; exact ha
      obtain ⟨t, ht⟩ := (irreducible_annihilator hq hbz hq' u).1 hu'
      exact ⟨t, by rw [hb, hu, ht]; ring⟩
    · rintro ⟨t, rfl⟩
      rw [mul_comm, act_mul, hb, mul_comm q b, act_mul, hqz, hyb, map_zero]
  · have hg1 : g = 1 := by rw [eq_C_of_natDegree_eq_zero (by omega : g.natDegree = 0), hc, C_1]
    exact ⟨0, by simp [hg1]⟩
termination_by g.natDegree

/-- Distinct multisets give different products when each generator has a
root which is a root of none of the others. -/
private theorem multiset_product_injective {ι : Type*} (G : ι → BinaryPoly)
    (hne : ∀ i, G i ≠ 0) (mark : ∀ i, ∃ z : K, ∀ j, aeval z (G j) = 0 ↔ i = j) :
    Function.Injective (fun s : Multiset ι => (s.map G).prod) := by
  classical
  intro s t he
  apply Multiset.ext.2
  intro i
  obtain ⟨z, hz⟩ := mark i
  let B (j : ι) := (G j).map (algebraMap (ZMod 2) K)
  have hn (j : ι) : B j ≠ 0 := Polynomial.map_ne_zero (hne j)
  have hr (j : ι) : (B j).IsRoot z ↔ i = j := by simpa [B, IsRoot, eval_map_algebraMap] using hz j
  let m := rootMultiplicity z (B i)
  have hm : 0 < m := (rootMultiplicity_pos (hn i)).2 ((hr i).2 rfl)
  have count (u : Multiset ι) : rootMultiplicity z ((u.map B).prod) = u.count i * m := by
    induction u using Multiset.induction_on with
    | empty => simp [rootMultiplicity_eq_zero (show ¬(1 : K[X]).IsRoot z by simp)]
    | cons j u ih =>
      have hprod : (u.map B).prod ≠ 0 := Multiset.prod_ne_zero (by simpa using fun j _ => hn j)
      rw [Multiset.map_cons, Multiset.prod_cons, rootMultiplicity_mul (mul_ne_zero (hn j) hprod), ih]
      by_cases hij : i = j
      · subst j
        rw [Multiset.count_cons_self, Nat.succ_mul, add_comm]
      · rw [Multiset.count_cons_of_ne hij, rootMultiplicity_eq_zero (fun h => hij ((hr j).1 h)), zero_add]
  have eq := congrArg (Polynomial.map (algebraMap (ZMod 2) K)) he
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def] at eq
  have hv := congrArg (rootMultiplicity z) eq
  change rootMultiplicity z ((s.map B).prod) = rootMultiplicity z ((t.map B).prod) at hv
  rw [count, count] at hv
  exact Nat.eq_of_mul_eq_mul_right hm hv

/-- Evaluation of any linearized quotient whose seed is nonzero modulo the
primitive seed belongs to the cyclic group generated by the lifted root. -/
theorem Primitive.oreLift_value_is_power {p g : BinaryPoly} (hp : Primitive p)
    (hg : ¬ p ∣ g) :
    ∃ e : ℕ, AdjoinRoot.mk (oreLift p) (oreLift g) = AdjoinRoot.root (oreLift p)^e := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero K (oreLift p) (ne_of_gt hp.irreducible_oreLift.degree_pos)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_aeval_zero', oreLift_constant, hp.coeff_zero_eq_one, map_one] at hx
    exact one_ne_zero hx
  have hp' : act p x = 0 := by rw [oreLift_frobenius, hx, mul_zero]
  have hz : act g x ≠ 0 := fun h => hg ((irreducible_annihilator hp.2.1 hx0 hp' g).1 h)
  have hz' : aeval (act g x) (oreLift p) = 0 := by
    have hk : act p (act g x) = 0 := by rw [act_comm, hp', map_zero]
    exact (mul_eq_zero.1 ((oreLift_frobenius p _).symm.trans hk)).resolve_left hz
  obtain ⟨a, ha⟩ := exists_frobenius_root hp.irreducible_oreLift hx hz'
  letI : Fact (Irreducible (oreLift p)) := ⟨hp.irreducible_oreLift⟩
  let φ := AdjoinRoot.liftAlgHom (oreLift p) (Algebra.ofId _ _) x hx
  refine ⟨2^a-1, φ.injective ?_⟩
  rw [map_pow]
  change φ (AdjoinRoot.mk (oreLift p) (oreLift g)) = (φ (AdjoinRoot.root (oreLift p)))^(2^a-1)
  rw [show φ (AdjoinRoot.root (oreLift p)) = x from AdjoinRoot.liftAlgHom_root ..]
  change aeval x (oreLift g) = x^(2^a-1)
  apply mul_left_cancel₀ hx0
  rw [← oreLift_frobenius, ← pow_succ', Nat.sub_add_cancel (Nat.two_pow_pos a)]
  exact ha

/-- Count h-fold products drawn from X and all 2^a linearized quotients
of monic degree-(a+1), constant-one binary polynomials. -/
theorem Primitive.oreLift_order_bound {p : BinaryPoly} (hp : Primitive p) (a h : ℕ)
    (ha : a+1 < p.natDegree) (hh : h*(2^(a+1)-1) < 2^p.natDegree-1) :
    (2^a+h).choose h ≤ orderOf (AdjoinRoot.root (oreLift p)) := by
  classical
  let I := Fin (2^a)
  let g (i : I) := decode (2*(2^a+i.val)+1)
  have gd (i : I) : (g i).natDegree = a+1 := by
    dsimp only [g]
    rw [natDegree_decode, Nat.log2_eq_iff (by omega)]
    simp only [pow_succ]
    have := i.isLt
    omega
  have gc (i : I) : (g i).coeff 0 = 1 := by simp [g, Nat.testBit_zero]
  have gn (i : I) : g i ≠ 0 := by intro e; have := gc i; simp [e] at this
  have gi : Function.Injective g := by
    intro i j he
    have := decode_injective he
    apply Fin.ext
    omega
  let G : Option I → BinaryPoly := fun j => j.elim X (fun i => oreLift (g i))
  have gne : ∀ j, G j ≠ 0
    | none => X_ne_zero
    | some i => oreLift_ne_zero (gn i)
  have gb : ∀ j, (G j).natDegree ≤ 2^(a+1)-1
    | none => by change X.natDegree ≤ _; rw [natDegree_X]; have := Nat.two_pow_pos a; rw [pow_succ]; omega
    | some i => by change (oreLift (g i)).natDegree ≤ _; rw [oreLift_degree (gn i), gd]
  have gm : ∀ i, ∃ z : K, ∀ j, aeval z (G j) = 0 ↔ i = j
    | none => ⟨0, fun j => by cases j with
        | none => simp [G]
        | some i => simp [G, ← coeff_zero_eq_aeval_zero', gc]⟩
    | some i => by
      obtain ⟨z, hz⟩ := exists_exact_frobenius_annihilator (g i) (gc i)
      have hz0 : z ≠ 0 := by
        rintro rfl
        have hdiv := (hz 1).1 (map_zero _)
        have hle := natDegree_le_of_dvd hdiv (one_ne_zero : (1 : BinaryPoly) ≠ 0)
        rw [gd, natDegree_one] at hle
        omega
      refine ⟨z, fun j => ?_⟩
      cases j with
      | none => simpa [G] using hz0
      | some j =>
        change aeval z (oreLift (g j)) = 0 ↔ some i = some j
        rw [Option.some.injEq, ← mul_eq_zero_iff_left hz0, ← oreLift_frobenius, hz]
        constructor
        · intro hd
          exact gi (eq_of_monic_of_dvd_of_natDegree_le (binary_monic (gn _)) (binary_monic (gn _))
            hd (by rw [gd, gd])).symm
        · rintro rfl; exact dvd_rfl
  have gp : ∀ j, ∃ e : ℕ, AdjoinRoot.mk (oreLift p) (G j) = AdjoinRoot.root (oreLift p)^e
    | none => ⟨1, by simp [G]⟩
    | some i => hp.oreLift_value_is_power (fun h =>
        (not_le_of_gt ((gd i).trans_lt ha)) (natDegree_le_of_dvd h (gn i)))
  choose e he using gp
  let S := Sym (Option I) h
  let rep (u : S) := (u.val.map G).prod
  let exp (u : S) := (u.val.map e).sum
  have hi : Function.Injective rep := fun _ _ eq => Subtype.ext (multiset_product_injective G gne gm eq)
  have hd (u : S) : (rep u).natDegree < (oreLift p).natDegree := by
    apply (natDegree_multiset_prod_le _).trans_lt
    rw [oreLift_degree hp.2.1.ne_zero]
    apply lt_of_le_of_lt _ hh
    rw [Multiset.map_map]
    have hle := Multiset.sum_le_card_nsmul (u.val.map (natDegree ∘ G)) (2^(a+1)-1)
      (by intro k hk; obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hk; exact gb j)
    simpa [u.property, nsmul_eq_mul] using hle
  have hr (u : S) : AdjoinRoot.mk (oreLift p) (rep u) = AdjoinRoot.root (oreLift p)^(exp u) := by
    simp only [rep, exp, map_multiset_prod, Multiset.map_map, Function.comp_def, he]
    generalize u.val = t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons j t ih => simp [ih, pow_add]
  have hc := order_ge_of_representatives (oreLift_constant p |>.trans hp.coeff_zero_eq_one) rep exp hi hd hr
  simpa [S, I, Sym.card_sym_eq_choose, Fintype.card_option, Nat.add_right_comm] using hc

/-- A root of an irreducible lift of degree n=2^s-1 has log-order
of size at least a constant times the square root of n. -/
theorem Primitive.oreLift_order_exponential {p : BinaryPoly} (hp : Primitive p)
    {a : ℕ} (ha : 2 ≤ a) (hs : 2*a+1 ≤ p.natDegree) :
    2^(2^(a+1)-a) < orderOf (AdjoinRoot.root (oreLift p)) := by
  let m := 2^a
  have hm : 4 ≤ m := Nat.pow_le_pow_right (by decide : 0 < 2) ha
  have hd := Nat.pow_le_pow_right (by decide : 0 < 2) hs
  have he : m*2^(a+1) = 2^(2*a+1) := by
    change 2^a* 2^(a+1) = _
    rw [← pow_add]; congr 1; omega
  have hh : m*(2^(a+1)-1) < 2^p.natDegree-1 := by
    rw [Nat.mul_sub, he, mul_one]
    have := Nat.one_lt_two_pow hp.2.1.natDegree_pos.ne'
    omega
  have hbin := hp.oreLift_order_bound a m (by omega) hh
  change (m+m).choose m ≤ _ at hbin
  rw [← two_mul, ← Nat.centralBinom_eq_two_mul_choose] at hbin
  apply lt_of_lt_of_le _ hbin
  apply Nat.lt_of_mul_lt_mul_left (a := m)
  have he' : m*2^(2^(a+1)-a) = 4^m := by
    change 2^a * 2^(2^(a+1)-a) = 4^m
    rw [← pow_add, show a + (2^(a+1)-a) = 2*m by
      have h := a.lt_two_pow_self; change a < m at h; rw [pow_succ]; omega]
    rw [pow_mul]; rfl
  rw [he']
  exact Nat.four_pow_lt_mul_centralBinom m hm

end GF2Sparse
