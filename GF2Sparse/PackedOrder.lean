import GF2Sparse.PackedSquare

/-! Packed squaring for arbitrary binary exponents and complete order-factor lists. -/

namespace GF2Sparse.PackedSquare

open Polynomial

/-- Process the low k bits from most to least significant, reducing after each bit. -/
def powerBits (width n fuel : ℕ) (stages : List (ℕ × ℕ)) (js : List ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => some 1
  | k+1, e =>
    match powerBits width n fuel stages js k (e/2) with
    | none => none
    | some a => if a < 2^width then
        let sq := spread stages a
        some (reduceHigh n js fuel (if e%2 = 1 then sq <<< 1 else sq))
      else none

theorem powerBits_sound {width n f fuel k e v : ℕ} {js : List ℕ} {stages : List (ℕ × ℕ)}
    (hc : checkBasis width stages = true) (hf : xorShifts js 1 = f) (he : e < 2^k)
    (hr : powerBits width n fuel stages js k e = some v) :
    AdjoinRoot.mk (decode f) (decode v) = AdjoinRoot.root (decode f)^e := by
  induction k generalizing e v with
  | zero =>
    have he0 : e = 0 := by simpa using he
    have hv : 1=v := Option.some.inj hr
    simp [he0, ← hv]
  | succ k ih =>
    cases hprev : powerBits width n fuel stages js k (e/2) with
    | none => simp [powerBits, hprev] at hr
    | some a =>
      simp only [powerBits, hprev] at hr
      by_cases hsmall : a < 2^width
      · rw [if_pos hsmall] at hr
        have hhalf : e/2 < 2^k := by rw [pow_succ] at he; omega
        have hsq := ih hhalf hprev
        rw [← Option.some.inj hr, mk_reduceHigh _ _ _ _ _ hf]
        split
        · rename_i hodd
          rw [decode_shift, decode_spread hc hsmall, map_mul, AdjoinRoot.mk_X, map_pow, hsq,
            ← pow_mul, ← pow_succ']
          congr 1
          omega
        · rw [decode_spread hc hsmall, map_pow, hsq, ← pow_mul]
          congr 1
          omega
      · simp [hsmall] at hr

private theorem reduced_ne_one {f r : ℕ} (hf : f ≠ 0) (hr : r ≠ 1)
    (hs : r < 2^f.log2) (hn : 0 < f.log2) : AdjoinRoot.mk (decode f) (decode r) ≠ 1 := by
  intro he
  have hne : r ^^^ 1 ≠ 0 := fun h => hr (Nat.xor_eq_zero_iff.1 h)
  have hd := (Nat.log2_lt hne).2 (Nat.xor_lt_two_pow hs (Nat.one_lt_two_pow hn.ne'))
  have hpoly := fun (h : decode (r ^^^ 1) = 0) => hne (decode_injective (h.trans decode_zero.symm))
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_decode hf) hpoly (by simpa only [natDegree_decode] using hd)
  rw [decode_xor, map_add, he, decode_one, map_one]
  simpa only [map_add, map_one, map_zero] using
    congrArg (AdjoinRoot.of (decode f)) (show (1 : ZMod 2) + 1 = 0 by decide)

def nontrivialPower (n fuel : ℕ) (stages : List (ℕ × ℕ)) (js : List ℕ) (e : ℕ) : Bool :=
  match powerBits n n fuel stages js (e.log2+1) e with
  | some v => v != 1 && v < 2^n
  | none => false

/-- A reduced nonidentity residue certifies a proper-power test for any tap list. -/
theorem nontrivialPower_sound {n fuel e f : ℕ} {stages : List (ℕ × ℕ)} {js : List ℕ}
    (hb : checkBasis n stages = true) (hf : xorShifts js 1 = f) (hd : f.log2 = n)
    (hn : 0 < n) (h : nontrivialPower n fuel stages js e = true) :
    AdjoinRoot.root (decode f)^e ≠ 1 := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hd; omega
  unfold nontrivialPower at h
  split at h
  · rename_i v hv
    rw [← powerBits_sound hb hf Nat.lt_log2_self hv]
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
    exact reduced_ne_one hf0 h.1 (hd ▸ h.2) (hd ▸ hn)
  · contradiction

/-- The factor list includes multiplicities. Test each distinct prime once. -/
def checkOrder (n u v : ℕ) (ps : List ℕ) : Bool :=
  let stages := stagesFor ((n-1).log2+1)
  let js := [n,u+v,u,v,0]
  let fuel := n/(n-(u+v))+2
  let m := 2^n-1
  (productMask n u v).log2 == n && ps.prod == m && checkBasis n stages &&
    run n n fuel stages js n 1 == some 1 &&
    ps.eraseDups.all fun p => nontrivialPower n fuel stages js (m/p)

/-- A successful packed check proves the full multiplicative order. -/
theorem primitive_product_of_checkOrder {n u v : ℕ} (hn : 0 < n) (ps : List ℕ)
    (hprime : ∀ p ∈ ps, p.Prime) (hc : checkOrder n u v ps = true) :
    Primitive (productCandidate n u v) := by
  let f := productMask n u v
  let js := [n,u+v,u,v,0]
  have hf : xorShifts js 1 = f := by simp [js, f, xorShifts, productMask, Nat.shiftLeft_eq, Nat.xor_assoc]
  simp only [checkOrder, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨hd, hp⟩, hb⟩, hfull⟩, hproper⟩ := hc
  have hdeg : (decode f).natDegree = n := (natDegree_decode f).trans hd
  have hf0 : f ≠ 0 := by intro hz; change f.log2 = n at hd; rw [hz] at hd; simp at hd; omega
  rw [← decode_productMask]
  apply primitive_of_prime_checks (monic_decode hf0) (hdeg ▸ hn)
  · rw [hdeg]
    have hone : AdjoinRoot.mk (decode f) (decode 1) = 1 := by simp
    have he := run_sound hb hf hfull (e := 1) (by decide) (by simpa only [Nat.sub_self, pow_zero] using hone)
    exact (by simpa only [Nat.mul_one] using he.symm.trans hone)
  · rw [hdeg]
    intro p hq hdiv
    have hm := mem_list_primes_of_dvd_prod hq.prime (fun q h => (hprime q h).prime) (hp ▸ hdiv)
    exact nontrivialPower_sound hb hf hd hn (hproper p (List.mem_eraseDups.2 hm))

def productEntry (n u v : ℕ) (primes : List ProvenPrime)
    (hc : checkOrder n u v (primes.map Subtype.val) = true)
    (hshape : 0 < u ∧ 0 < v ∧ u ≠ v ∧ u+v < n := by decide) :
    {k : ℕ // HasPrimitiveProduct k} := by
  obtain ⟨hu,hv,huv,ht⟩ := hshape
  refine ⟨n,u,v,hu,hv,huv,ht,primitive_product_of_checkOrder (by omega) _ ?_ hc⟩
  intro p hp
  obtain ⟨q,_,rfl⟩ := List.mem_map.1 hp
  exact q.property

end GF2Sparse.PackedSquare
