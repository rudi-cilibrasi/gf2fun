import GF2Sparse.OreLift
import GF2Sparse.PackedOrder
import GF2Sparse.Table
import GF2Sparse.MersenneDivisors

/-! Field powers, the index floor, and the exact character-sum arithmetic
for the projected logarithms at the root of X^2047 + X^511 + 1. -/

namespace GF2Sparse.OreCircle2047
open Polynomial PackedSquare

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 4096

private def p47 : ProvenPrime := ⟨47, by norm_num1⟩
private def p2 : ProvenPrime := ⟨2, by norm_num1⟩
private def p23 : ProvenPrime := ⟨23, by norm_num1⟩
private def p89 : ProvenPrime := ⟨89, by norm_num1⟩
private def p131009 : ProvenPrime := lucasPrime 131009 6 [p2, p2, p2, p2, p2, p2, p23, p89] (by decide +kernel)
private def p5 : ProvenPrime := ⟨5, by norm_num1⟩
private def p97 : ProvenPrime := ⟨97, by norm_num1⟩
private def p178481 : ProvenPrime := lucasPrime 178481 3 [p2, p2, p2, p2, p5, p23, p97] (by decide +kernel)
private def p3 : ProvenPrime := ⟨3, by norm_num1⟩
private def p59 : ProvenPrime := ⟨59, by norm_num1⟩
private def p724639 : ProvenPrime := lucasPrime 724639 3 [p2, p3, p23, p59, p89] (by decide +kernel)
private def p41 : ProvenPrime := ⟨41, by norm_num1⟩
private def p31 : ProvenPrime := ⟨31, by norm_num1⟩
private def p5023 : ProvenPrime := lucasPrime 5023 3 [p2, p3, p3, p3, p3, p31] (by decide +kernel)
private def p2529391927 : ProvenPrime := lucasPrime 2529391927 3 [p2, p3, p23, p41, p89, p5023] (by decide +kernel)
private def p227 : ProvenPrime := ⟨227, by norm_num1⟩
private def p911 : ProvenPrime := ⟨911, by norm_num1⟩
private def p7 : ProvenPrime := ⟨7, by norm_num1⟩
private def p149 : ProvenPrime := ⟨149, by norm_num1⟩
private def p2087 : ProvenPrime := lucasPrime 2087 5 [p2, p7, p149] (by decide +kernel)
private def p7605029 : ProvenPrime := lucasPrime 7605029 2 [p2, p2, p911, p2087] (by decide +kernel)
private def p15210059 : ProvenPrime := lucasPrime 15210059 2 [p2, p7605029] (by decide +kernel)
private def p70676429054711 : ProvenPrime := lucasPrime 70676429054711 17 [p2, p5, p23, p89, p227, p15210059] (by decide +kernel)
private def p17 : ProvenPrime := ⟨17, by norm_num1⟩
private def p353 : ProvenPrime := ⟨353, by norm_num1⟩
private def p397 : ProvenPrime := ⟨397, by norm_num1⟩
private def p683 : ProvenPrime := ⟨683, by norm_num1⟩
private def p11 : ProvenPrime := ⟨11, by norm_num1⟩
private def p2113 : ProvenPrime := lucasPrime 2113 5 [p2, p2, p2, p2, p2, p2, p3, p11] (by decide +kernel)
private def p239 : ProvenPrime := ⟨239, by norm_num1⟩
private def p1913 : ProvenPrime := lucasPrime 1913 3 [p2, p2, p2, p239] (by decide +kernel)
private def p29 : ProvenPrime := ⟨29, by norm_num1⟩
private def p1451 : ProvenPrime := lucasPrime 1451 2 [p2, p5, p5, p29] (by decide +kernel)
private def p8707 : ProvenPrime := lucasPrime 8707 5 [p2, p3, p1451] (by decide +kernel)
private def p2931542417 : ProvenPrime := lucasPrime 2931542417 3 [p2, p2, p2, p2, p11, p1913, p8707] (by decide +kernel)
private def p618970019642690137449562111 : ProvenPrime := lucasPrime 618970019642690137449562111 3 [p2, p3, p5, p17, p23, p89, p353, p397, p683, p2113, p2931542417] (by decide +kernel)

private def factors : List ProvenPrime := [p47, p131009, p178481, p724639, p2529391927, p70676429054711, p618970019642690137449562111]

def knownPart : ℕ := (factors.map Subtype.val).prod
def cofactor : ℕ := (2^2047-1) / knownPart

theorem decomposition : knownPart * cofactor = 2^2047-1 ∧ knownPart.Coprime cofactor ∧
    cofactor.Coprime ((2^23-1)*(2^89-1)) := by decide +kernel

private def taps : List ℕ := [2047,511,0]
private abbrev mask := xorShifts taps 1
private def stages := stagesFor 11
private theorem basis : checkBasis 2047 stages = true := by decide +kernel
private theorem decoded : decode mask = trinomial 2047 511 := by
  simp only [mask, taps, xorShifts, decode_xor, decode_shift_by, decode_one, decode_zero,
    pow_zero, mul_one, add_zero, trinomial]

theorem irreducible : Irreducible (trinomial 2047 511) := by
  have hs := (check_sound (n := 11) (f := 0xa01) (factors := [23,89])
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> decide) (by decide +kernel)).2.2
  have he : oreLift (decode (2^11 ^^^ (2^9 ^^^ 1))) = trinomial (2^11-1) (2^9-1) := by
    simp only [decode_xor, decode_one, decode_pow_two, oreLift_add, oreLift_X_pow, oreLift_one, trinomial]
  exact he ▸ hs.irreducible_oreLift

/-- The two norm circles use the same parameter at every root of the trinomial. -/
theorem circle_parameter {K : Type*} [Field K] [CharP K 2] {r : K}
    (hz : r^2047 + (r^511 + 1) = 0) :
    (r^512)^4 + r^512 = r ∧ (r^512)^2 = r^1024 := by
  have h : r^2047 + r^511 = 1 := by
    rw [← add_assoc] at hz
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left hz
  constructor
  · calc
      (r^512)^4 + r^512 = r*(r^2047+r^511) := by ring
      _ = r := by rw [h, mul_one]
  · rw [← pow_mul]

private theorem powers : (factors.map Subtype.val).all (fun p =>
    nontrivialPower 2047 3 stages taps (cofactor*(knownPart/p))) = true := by decide +kernel

/-- Projecting onto the part of the order with a complete factorization. -/
theorem projected_order : orderOf (AdjoinRoot.root (trinomial 2047 511)^cofactor) = knownPart := by
  rw [← decoded]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide +kernel)
  · rw [← pow_mul, Nat.mul_comm, decomposition.1]
    have h := powerBits_sound (n := 2047) (e := 2^2047-1) (v := 1) basis (show xorShifts taps 1 = mask from rfl)
      Nat.lt_log2_self (fuel := 3) (by decide +kernel)
    simpa using h.symm
  · intro p hp hdiv
    have hprime : ∀ q ∈ factors.map Subtype.val, Prime q := by
      intro q hq
      obtain ⟨v, _, rfl⟩ := List.mem_map.1 hq
      exact v.property.prime
    have hmem := mem_list_primes_of_dvd_prod hp.prime hprime hdiv
    rw [← pow_mul]
    exact nontrivialPower_sound basis rfl (by decide +kernel : mask.log2 = 2047)
      (by decide) (List.all_eq_true.1 powers p hmem)

theorem known_dvd_order : knownPart ∣ orderOf (AdjoinRoot.root (trinomial 2047 511)) :=
  projected_order ▸ orderOf_pow_dvd (x := AdjoinRoot.root (trinomial 2047 511)) cofactor

private theorem candidates :
    (List.range 244).all (fun k => cofactor % (4094*(k+1)+1) != 0) = true := by decide +kernel

private theorem even_predecessor {p : ℕ} (h : p % 8 = 1 ∨ p % 8 = 7) : 2 ∣ p-1 := by omega

private theorem trial_index {p j : ℕ} (hp : 2 ≤ p) (hle : p ≤ 1000000) (hj : p-1 = 4094*j) :
    j-1 < 244 ∧ 4094*(j-1+1)+1 = p := by omega

/-- No prime at most one million divides the remaining cofactor. -/
theorem cofactor_prime_gt {p : ℕ} (hp : p.Prime) (hd : p ∣ cofactor) : 1000000 < p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hM : p ∣ 2^2047-1 := decomposition.1 ▸ hd.trans (dvd_mul_left _ _)
  have hmod (n : ℕ) : (2 : ZMod p)^n = 1 ↔ p ∣ 2^n-1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.two_pow_pos n), Nat.cast_pow,
        Nat.cast_ofNat, Nat.cast_one, sub_eq_zero]
  have hpow := (hmod 2047).2 hM
  have hsmall (n : ℕ) (hn : n = 23 ∨ n = 89) : (2 : ZMod p)^n ≠ 1 := by
    intro h
    have hh := (hmod n).1 h
    have hboth : p ∣ (2^23-1)*(2^89-1) := by
      rcases hn with rfl | rfl
      · exact hh.trans (dvd_mul_right _ _)
      · exact hh.trans (dvd_mul_left _ _)
    exact hp.not_dvd_one (decomposition.2.2.gcd_eq_one ▸ Nat.dvd_gcd hd hboth)
  have ho : orderOf (2 : ZMod p) = 2047 := by
    have hdiv := orderOf_dvd_of_pow_eq_one hpow
    have possibilities : (List.range 2048).all (fun d => decide
        (d ∣ 2047 → d = 1 ∨ d = 23 ∨ d = 89 ∨ d = 2047)) = true := by decide +kernel
    have hlt := Nat.lt_succ_of_le (Nat.le_of_dvd (by decide : 0 < 2047) hdiv)
    have hmem := of_decide_eq_true (List.all_eq_true.1 possibilities _ (List.mem_range.2 hlt))
    rcases hmem hdiv with h | h | h | h
    · exact (hsmall 23 (Or.inl rfl) (orderOf_dvd_iff_pow_eq_one.1 (by simp [h]))).elim
    · exact (hsmall 23 (Or.inl rfl) (orderOf_dvd_iff_pow_eq_one.1 (by simp [h]))).elim
    · exact (hsmall 89 (Or.inr rfl) (orderOf_dvd_iff_pow_eq_one.1 (by simp [h]))).elim
    · exact h
  have h8 := odd_mersenne_prime_mod_eight (by decide : Odd 2047) hp hM
  have hne : (2 : ZMod p) ≠ 0 := by
    intro he
    simp [he] at hpow
  have hdiv := orderOf_dvd_of_pow_eq_one (FiniteField.pow_card_sub_one_eq_one (2 : ZMod p) hne)
  rw [ho, ZMod.card] at hdiv
  have hdbl := even_predecessor h8
  obtain ⟨j,hj⟩ : 4094 ∣ p-1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 2047) hdbl hdiv
  by_contra! hle
  obtain ⟨hlt, he⟩ := trial_index hp.two_le hle hj
  have htest := List.all_eq_true.1 candidates (j-1) (List.mem_range.2 hlt)
  rw [he] at htest
  simp [Nat.mod_eq_zero_of_dvd hd] at htest

private def counts : List (ℕ × ℕ) :=
  [(1,2),(2,1),(3,2),(4,3),(5,6),(6,9),(9,56),(10,99),(18,14532),(20,52377)]

private def b (k : ℕ) := (counts.map (fun ⟨d,c⟩ => if k%d = 0 then d*c else 0)).sum
private def w (i : ℕ) := (i+1)*(64-i)*(if i%2 = 0 then 5 else 7)
private def cross (k : ℕ) := ((List.range (64-k)).map fun i =>
  w i * w (i+k) * 2^(32-(k+i%2+(i+k)%2)/2)).sum

/-- Numerator and denominator after clearing the common powers of two in the moment bound. -/
def numerator : ℤ := ((List.range 63).map fun j =>
  let k := j+1
  (2*cross k : ℤ) * (((1+b k)*999999+b k : ℕ) - (2^k : ℤ))).sum

def denominator : ℕ := 999999 * ((List.range 64).map fun i => (w i)^2 * 2^(32-i%2)).sum

theorem moment_arithmetic :
    (counts.map Prod.snd).sum = 67087 ∧ 0 < denominator ∧
    numerator*3893285176287122423808 = (denominator : ℤ)*8528049275675000138708959 ∧
    2045*(denominator : ℤ) < numerator := by decide +kernel

end GF2Sparse.OreCircle2047
