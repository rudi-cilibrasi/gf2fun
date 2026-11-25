import GF2Sparse.Table
import Mathlib.NumberTheory.LucasLehmer

/-! Primitive witnesses from the even- and odd-degree families in the
factor-parity sieve. The exact order certificates are independent of the
paper parity argument. -/

namespace GF2Sparse

open Polynomial

set_option maxRecDepth 8192

private def fiveTermMask (n c b a : ℕ) : ℕ :=
  2 ^ n ^^^ 2 ^ c ^^^ 2 ^ b ^^^ 2 ^ a ^^^ 1

private theorem certify_five_terms (n c b a : ℕ) (ps : List ℕ)
    (hp : ∀ p ∈ ps, Nat.Prime p) (h : check n (fiveTermMask n c b a) ps = true) :
    Primitive (X ^ n + X ^ c + X ^ b + X ^ a + 1) := by
  simpa only [fiveTermMask, decode_xor, decode_pow_two, decode_one] using
    (check_sound hp h).2.2

private theorem prime_3173389601 : Nat.Prime 3173389601 := by
  let two : ProvenPrime := ⟨2, by decide⟩
  let five : ProvenPrime := ⟨5, by decide⟩
  exact (lucasPrime 3173389601 6 [two, two, two, two, two, five, five,
    ⟨571, by norm_num1⟩, ⟨6947, by norm_num1⟩] (by decide +kernel)).property

theorem parity_example_200 : Primitive (X ^ 200 + X ^ 56 + X ^ 17 + X ^ 2 + 1) := by
  apply certify_five_terms 200 56 17 2
    [3, 5, 5, 5, 11, 17, 31, 41, 101, 251, 401, 601, 1801, 4051, 8101, 61681,
      268501, 340801, 2787601, 3173389601]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h <;> rw [h] <;> first | exact prime_3173389601 | norm_num1
  · decide +kernel

private def checkBlocks (s : ℕ → ℕ) (a : ℕ) : List (ℕ × ℕ) → Bool
  | [] => a == 1
  | (k, b) :: rest => (s^[k] a == b) && checkBlocks s b rest

private theorem checkBlocks_sound (s : ℕ → ℕ) (a : ℕ) (blocks : List (ℕ × ℕ))
    (h : checkBlocks s a blocks = true) : s^[(blocks.map Prod.fst).sum] a = 1 := by
  induction blocks generalizing a with
  | nil => simpa [checkBlocks] using h
  | cons head rest ih =>
    obtain ⟨k, b⟩ := head
    obtain ⟨hb, hr⟩ := Bool.and_eq_true_iff.1 h
    rw [List.map_cons, List.sum_cons, Nat.add_comm, Function.iterate_add_apply, beq_iff_eq.1 hb]
    exact ih b hr

private def blocks521 : List (ℕ × ℕ) := [
  (64, 0xc404fe848c9719e8441dd398f090b6c78c24880422cd46c64a4b8dc48fcf4eb2fd146bdac36752cc7b9d13d7fa35f93b26a3b568741a76da9fa62222b37a64b3be),
  (64, 0xfcc7f4ab502d6486a7af4d5b89a5def757566315de4e2134bce58eae6cdf9240ff65aa12d6c4ce220fa468b65a91a62d20ee844d78982694be195ea19c789b4bef),
  (64, 0x1009cfed8a7712036cf05c2488bc8a2374c21e2214fd5ce270d75ac3779c94f811a528deb20e3533b006d5df5981d288fe83fb825efadc863235679c6f5397eb4a4),
  (64, 0x11899528bb200c79fdbb11d46bfa1d02d07b267a062718ef026a1e03a12f899a57d516ef50544d6f42f40eed073be6f36a02435a55c659e8eb42a5b59a016b50aed),
  (64, 0x744496a0fe73c4c7b8f610cf572bc249d697125394501aa4dfbd49ae071a00588599390ecbad76358eb11fa9166be3988f8d843d1ed930d24ecb8225e8322bfd37),
  (64, 0x10f327af49a8d756ce4cd78dab8ba2d1f859ae5c1550b28af7c078a83713ea9ed09643c187ca55caaeeb964882bb0ba6335cb4e260a59060c1d65d6780753b330cf),
  (64, 0x5808af9ab2bef4de76d7293c63aa6506bd7e7745271ff16afe128983ea09811509972ef4ed708d0f52fb8780978b888611092188dd282f50060aff6331ff37fb77),
  (64, 0x1f74323f9799d01b17e42f8d2f07070ea51ff094945e4f7bfee4baeaa9d176ae4b13875efacbfeaf29174040e73e600b002dd0be0a1bb6e422cdf9a6f5a3bce97d5),
  (9, 1)]

private theorem full_power_521 :
    xPow 521 (fiveTermMask 521 416 282 8) (2 ^ 521 - 1) = 1 := by
  rw [xPow_mersenne _ _ _ (by decide)]
  exact checkBlocks_sound _ 1 blocks521 (by decide +kernel)

theorem parity_example_521 : Primitive (X ^ 521 + X ^ 416 + X ^ 282 + X ^ 8 + 1) := by
  apply certify_five_terms 521 416 282 8 [2 ^ 521 - 1]
  · intro p hp
    rw [List.mem_singleton] at hp
    rw [hp]
    exact lucas_lehmer_sufficiency 521 (by decide) (by norm_num)
  · simp only [check, full_power_521]
    decide +kernel

/-- The sums over all unordered pairs of list positions, including doubles. -/
def unorderedSums : List ℕ → List ℕ
  | [] => []
  | x :: xs => (x :: xs).map (x + ·) ++ unorderedSums xs

theorem sidon_of_exponent_gaps {a b c n : ℕ} (ha : 0 < a) (hb : 2 * a < b)
    (hc : 2 * b < c) (hn : 2 * c < n) : (unorderedSums [0, a, b, c, n]).Nodup := by
  simp [unorderedSums, List.nodup_cons]
  repeat' apply And.intro
  all_goals omega

theorem sidon_of_odd_degree_shape {h c n : ℕ} (hh : Odd h) (hc : 8 ∣ c) (hn : Odd n)
    (h₁ : 16 < 2 * h) (h₂ : 8 + 2 * h < c) (h₃ : c < n) (h₄ : n < 4 * h) :
    (unorderedSums [0, 8, 2 * h, c, n]).Nodup := by
  obtain ⟨s, rfl⟩ := hh
  obtain ⟨u, rfl⟩ := hc
  obtain ⟨v, rfl⟩ := hn
  simp [unorderedSums, List.nodup_cons]
  repeat' apply And.intro
  all_goals omega

private theorem sidon12_checks : ∀ a b c : Fin 12,
    0 < a.val → a.val < b.val → b.val < c.val →
    (unorderedSums [0, a.val, b.val, c.val, 12]).Nodup →
    let f := fiveTermMask 12 c.val b.val a.val
    f ≠ 0 ∧ f.log2 = 12 ∧ excludesFullOrder 12 f 1365 = true := by decide +kernel

/-- In degree 12 none of the normalized pentanomials with Sidon support
has full multiplicative order. -/
theorem no_primitive_sidon_12 {a b c : ℕ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hc : c < 12) (hs : (unorderedSums [0, a, b, c, 12]).Nodup) :
    ¬ Primitive (X ^ 12 + X ^ c + X ^ b + X ^ a + 1) := by
  obtain ⟨hf, hd, h⟩ := sidon12_checks ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, hc⟩ ha hab hbc hs
  have he := excludesFullOrder_sound (by decide : 0 < 12) hf hd
    (by decide : 0 < 1365) (by decide) h
  simpa only [fiveTermMask, decode_xor, decode_pow_two, decode_one] using he

end GF2Sparse
