import GF2Sparse.FrobeniusWitness
import GF2Sparse.OreLift

/-! Two degree-2047 Ore lifts have a missing factor of 47 in their orders.
The 47th-root masks are reproduced by scripts/check_ore_2047.py --lean-rows. -/

namespace GF2Sparse

open Polynomial

set_option maxRecDepth 32768
set_option maxHeartbeats 1500000

private def certificates : List ((ℕ × ℕ × ℕ) × ℕ) := [
  ((2, 3, 7), 0x22a0394ecf0a572e0943391f73e297c9a40fabf7e2fe38ac6a72874ac7a238fa2a23b4813594494b8d903d533de57cc9efb5340c99777baf44d168ebd491d9eca1e02f92ea9a633dc5c4288aba392e763d57c3da74576f9028e30b7f7a6d7c2a56e0c682ebb649d0f54a9275629e63c896f5206f1c2db0ffae1cac97297dab85db564a728429755c740b95671524f94c2ebfc42815dbd67cbb7f001e92e368faf0ce0688f83fe1ec8c851a46e2779ee7caadbcfc16e8526360ce8e1f05e68dbc24cd82cfdb5429de411d140ce4c91f2d269fcbbba7a7f1f87d85fc53b90cc4ae36c4760cea9cec6ba4cc9693c972149a3d29fbc9070416d8b18d7a9babc30e4d),
  ((4, 8, 9), 0x61c20ae4806ae30e91a35f2beb5499d23cd70015aafa3090ff33a36e784ca342098b802897a47ba8103d4cef59afac57d4cd77fdfe38a8867286e5c867463c2b8165e75caec9984a063b58f297918e0d06defc30c3b905f77828a22907965746c3fd0608da5cba4be73fcae06c8360011adca83453ee8af86484a8c9ca94b598c6a0e4d3437126ffec103fffa27fce050a4d29044cc49f196bdfc8d4fcfba8719435c51e8fc7afb4ca634015a7dd6535c7dd318baf413480838de2a03f54cbce785976f48d0730963d9ddf2d8253b5334b3a9678139339a2a8b9d9f0dc7b339c41050d9403809226b659142ef499c69c7ec5c2e35a34fb83ed254d01ae5f940c)]

private def liftMask (a b c : ℕ) := fiveTermMask 2047 (2^c-1) (2^b-1) (2^a-1)

private def checks (row : (ℕ × ℕ × ℕ) × ℕ) : Bool :=
  let (a,b,c) := row.1
  let f := liftMask a b c
  check 11 (fiveTermMask 11 c b a) [23,89] && f.log2 == 2047 &&
    rootPowerCheck 47 2047 f row.2 12 [2047,2^c-1,2^b-1,2^a-1,0]

private theorem verified : certificates.all checks = true := by decide +kernel

set_option exponentiation.threshold 2047 in
theorem ore_degree_eleven_missing_forty_seven (a b c : ℕ)
    (hs : (a,b,c) ∈ [(2,3,7),(4,8,9)]) :
    let P := decode (fiveTermMask 11 c b a)
    Primitive P ∧ Irreducible (oreLift P) ∧
      orderOf (AdjoinRoot.root (oreLift P)) ∣ (2^2047-1)/47 ∧ ¬ Primitive (oreLift P) := by
  have hmem : (a,b,c) ∈ certificates.map Prod.fst := hs
  obtain ⟨⟨t,w⟩, hin, ht⟩ := List.mem_map.1 hmem
  change t = (a,b,c) at ht
  subst t
  have h := List.all_eq_true.1 verified _ hin
  simp only [checks, Bool.and_eq_true, beq_iff_eq] at h
  have hp := (check_sound (by
    intro p h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide) h.1.1).2.2
  have he : oreLift (decode (fiveTermMask 11 c b a)) = decode (liftMask a b c) := by
    simp only [liftMask, decode_fiveTermMask, oreLift_add, oreLift_X_pow, oreLift_one]
    rfl
  have hc : (decode (liftMask a b c)).coeff 0 = 1 := by
    rw [← he, oreLift_constant, hp.coeff_zero_eq_one]
  have hd := order_dvd_of_rootPowerCheck (m := 47) (n := 2047) (he ▸ hp.irreducible_oreLift)
    h.1.2 hc (by decide) (by decide +kernel) h.2
  refine ⟨hp, hp.irreducible_oreLift, he ▸ hd, ?_⟩
  intro hp'
  have ho := hp'.2.2
  rw [he, natDegree_decode, h.1.2] at ho
  rw [ho] at hd
  exact (by decide +kernel : ¬(2^2047-1) ∣ (2^2047-1)/47) hd

end GF2Sparse
