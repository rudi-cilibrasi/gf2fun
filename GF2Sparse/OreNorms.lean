import GF2Sparse.OreLift
import GF2Sparse.CompositionNorm
import Mathlib.LinearAlgebra.Vandermonde

/-! Computing Ore-root norms from seed residues and recovering the exact
Frobenius annihilator from a geometric expansion of the conjugates. -/

namespace GF2Sparse

open Polynomial FiniteField

variable {K : Type*} [Field K] [Algebra (ZMod 2) K]

/-- A small residue in the seed quotient gives a possibly very distant
Frobenius conjugate of any root of the lift. -/
theorem ore_conjugate_of_seed_remainder {p q : BinaryPoly} {z : K}
    (hz : aeval z (oreLift p) = 0) {k : ℕ} (h : p ∣ X^k-q) :
    z^(2^k) = z * aeval z (oreLift q) := by
  let F := (frobeniusAlgHom (ZMod 2) K).toLinearMap
  have hp : aeval F p z = 0 := by rw [show F = _ from rfl, oreLift_frobenius, hz, mul_zero]
  obtain ⟨u, hu⟩ := h
  have hkill : aeval F (X^k-q) z = 0 := by
    rw [hu, mul_comm, map_mul, Module.End.mul_apply, hp, map_zero]
  simpa only [map_sub, map_pow, aeval_X, LinearMap.sub_apply, sub_eq_zero,
    F, binary_frobenius_pow_apply, oreLift_frobenius] using hkill

/-- The relative norm exponent can be evaluated with one lifted linearized
polynomial for each seed remainder. -/
theorem ore_norm_of_seed_remainders {p : BinaryPoly} {z : K} (hz : aeval z (oreLift p) = 0)
    (m t : ℕ) (q : ℕ → BinaryPoly) (h : ∀ j < t, p ∣ X^(m*j)-q j) :
    z ^ normExponent (2^m) t = ∏ j ∈ Finset.range t, (z * aeval z (oreLift (q j))) := by
  rw [normExponent, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← pow_mul]
  exact ore_conjugate_of_seed_remainder hz (h j (Finset.mem_range.1 hj))

/-- If the ambient group size is A*B, raising to the norm exponent A
retains exactly the part of the multiplicative index visible in size B. -/
theorem norm_index_eq_gcd {M : Type*} [Monoid M] (x : M) {A B : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hd : orderOf x ∣ A*B) :
    B / orderOf (x^A) = ((A*B)/orderOf x).gcd B := by
  let h := orderOf x
  let I := A*B/h
  have hh : 0 < h := Nat.pos_of_dvd_of_pos hd (Nat.mul_pos hA hB)
  have hI : I*h = A*B := Nat.div_mul_cancel hd
  have hg : I.gcd B * h = h.gcd A * B := calc
    _ = (I*h).gcd (B*h) := (Nat.gcd_mul_right _ _ _).symm
    _ = (A*B).gcd (h*B) := by rw [hI, Nat.mul_comm B h]
    _ = _ := by rw [Nat.gcd_mul_right, Nat.gcd_comm A h]
  have hm : orderOf (x^A) * I.gcd B = B := by
    rw [orderOf_pow' x hA.ne']
    change (h/h.gcd A) * I.gcd B = B
    apply Nat.eq_of_mul_eq_mul_left (Nat.gcd_pos_of_pos_left A hh)
    rw [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left h A), Nat.mul_comm h]
    exact hg
  have hp : 0 < orderOf (x^A) :=
    Nat.pos_of_dvd_of_pos ((orderOf_pow_dvd (x := x) A).trans hd) (Nat.mul_pos hA hB)
  calc
    B / orderOf (x^A) = (orderOf (x^A) * I.gcd B) / orderOf (x^A) := congrArg (· / _) hm.symm
    _ = _ := Nat.mul_div_cancel_left _ hp

private theorem spectral_shift {t : ℕ} {z : K} {a c : Fin t → K}
    (hz : ∀ k : ℕ, z^(2^k) = ∑ i, c i * (a i)^k) (p : BinaryPoly) (k : ℕ) :
    aeval (frobeniusAlgHom (ZMod 2) K).toLinearMap p (z^(2^k)) =
      ∑ i, (c i * aeval (a i) p) * (a i)^k := by
  have he (j : ℕ) : (z^(2^k))^(2^j) = ∑ i, c i * (a i)^(k+j) := by
    rw [← pow_mul, ← pow_add, hz]
  rw [aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, binary_frobenius_pow_apply, he,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [aeval_eq_sum_range, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Algebra.smul_def, pow_add]
  ring

variable [CharP K 2]

/-- A binary polynomial annihilates an element under Frobenius exactly
when it vanishes at every distinct node in its geometric expansion. -/
theorem frobenius_annihilator_of_expansion {t : ℕ} {z : K} {a c : Fin t → K}
    (ha : Function.Injective a) (hc : ∀ i, c i ≠ 0)
    (hz : ∀ k : ℕ, z^(2^k) = ∑ i, c i * (a i)^k) (p : BinaryPoly) :
    aeval (frobeniusAlgHom (ZMod 2) K).toLinearMap p z = 0 ↔ ∀ i, aeval (a i) p = 0 := by
  constructor
  · intro h
    have hv : (fun i => c i * aeval (a i) p) = 0 :=
      Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ha fun k => by
        rw [← spectral_shift hz p (k : ℕ), oreLift_frobenius, aeval_dyadic, ← mul_pow,
          ← oreLift_frobenius, h, zero_pow (Nat.two_pow_pos _).ne']
    intro i
    exact (mul_eq_zero.1 (congrFun hv i)).resolve_left (hc i)
  · intro h
    simpa [h] using spectral_shift hz p 0

/-- The period of the element is the least common multiple of the
multiplicative orders of the nodes. -/
theorem frobenius_fixed_iff_nodes {t : ℕ} {z : K} {a c : Fin t → K}
    (ha : Function.Injective a) (hc : ∀ i, c i ≠ 0)
    (hz : ∀ k : ℕ, z^(2^k) = ∑ i, c i * (a i)^k) (d : ℕ) :
    z^(2^d) = z ↔ ∀ i, (a i)^d = 1 := by
  simpa [sub_eq_zero, binary_frobenius_pow_apply] using
    frobenius_annihilator_of_expansion ha hc hz ((X : BinaryPoly)^d-1)

/-- Sums indexed by all nonzero binary coefficient vectors. Repetitions
are retained, so the definition also applies to a dependent list. -/
def nonemptyBinarySums {A : Type*} [Add A] : List A → List A
  | [] => []
  | x::xs => x :: (nonemptyBinarySums xs ++ (nonemptyBinarySums xs).map (· + x))

private theorem nonemptyBinarySums_map {A B : Type*} [AddMonoid A] [AddMonoid B]
    (f : A →+ B) (xs : List A) :
    nonemptyBinarySums (xs.map f) = (nonemptyBinarySums xs).map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [nonemptyBinarySums, ih, List.map_map, Function.comp_def]

/-- Multiply all nonzero binary combinations by eliminating one basis
element at each step. -/
def binarySubspaceProduct {A : Type*} [CommRing A] : List A → A
  | [] => 1
  | x::xs => x * binarySubspaceProduct (xs.map fun y => y*(y+x))
termination_by xs => xs.length

theorem binarySubspaceProduct_eq {A : Type*} [CommRing A] [CharP A 2] (xs : List A) :
    binarySubspaceProduct xs = (nonemptyBinarySums xs).prod := by
  cases xs with
  | nil => rw [binarySubspaceProduct]; rfl
  | cons x xs =>
    let T : A →+ A :=
      { toFun := fun y => y*(y+x)
        map_zero' := by simp
        map_add' := fun a b => by
          have h (v : A) : v*(v+x) = v^2+v*x := by ring
          simp only [h, CharTwo.add_sq, add_mul]
          ring }
    rw [binarySubspaceProduct]
    change x * binarySubspaceProduct (xs.map T) = _
    rw [binarySubspaceProduct_eq (xs.map T), nonemptyBinarySums_map]
    simp only [nonemptyBinarySums, List.prod_cons, List.prod_append]
    change x * ((nonemptyBinarySums xs).map (fun y => y*(y+x))).prod = _
    simp only [List.prod_map_mul, List.map_id_fun', id_eq]
termination_by xs.length

end GF2Sparse
