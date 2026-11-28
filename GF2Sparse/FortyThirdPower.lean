import GF2Sparse.SafePrimePowers

/-! The exceptional pentanomial for the 43rd power has root order 129.
Its iterated cubic dilations have prescribed orders before and after powering. -/

namespace GF2Sparse

theorem order_129_of_pentanomial {K : Type*} [Field K] [CharP K 2] {z : K}
    (h : z^14 + z^9 + z^7 + z^5 + 1 = 0) : orderOf z = 129 := by
  have hquad : (z^43)^2 + z^43 + 1 = 0 := by
    calc
      _ = (z^72+z^67+z^65+z^63+z^62+z^57+z^55+z^54+z^52+z^51+z^48+
        z^44+z^43+z^42+z^40+z^37+z^36+z^35+z^32+z^30+z^29+z^28+
        z^24+z^21+z^20+z^18+z^17+z^15+z^10+z^9+z^7+z^5+1) *
        (z^14+z^9+z^7+z^5+1) := by ring_nf; reduce_mod_char!
      _ = 0 := by rw [h, mul_zero]
  have hfull : z^129 = 1 := by
    apply sub_eq_zero.mp
    calc
      _ = (z^43-1)*((z^43)^2+z^43+1) := by ring
      _ = 0 := by rw [hquad, mul_zero]
  have h43 : z^43 ≠ 1 := by
    intro hbad
    rw [hbad] at hquad
    reduce_mod_char! at hquad
    exact one_ne_zero hquad
  have h3 : z^3 ≠ 1 := by
    intro hbad
    have hz : z = 0 := by
      calc
        z = (z^14+z^9+z^7+z^5+1) -
          (z^3-1)*(z^11+z^8+z^6+z^5+z^4+z^3+z+1) := by ring_nf; reduce_mod_char!
        _ = 0 := by rw [h, hbad]; ring
    simp [hz] at hfull
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 129) hfull
  intro p hp hdvd
  rcases hp.dvd_mul.mp (show p ∣ 3 * 43 from hdvd) with hp3 | hp43
  · have heq := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp hp3
    simpa [heq] using h43
  · have heq := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43)).mp hp43
    simpa [heq] using h3

theorem order_43rd_power_dilations {K : Type*} [Field K] [CharP K 2] (z : K) (j : ℕ)
    (h : (z^(3^j))^14 + (z^(3^j))^9 + (z^(3^j))^7 + (z^(3^j))^5 + 1 = 0) :
    orderOf z = 129 * 3^j ∧ orderOf (z^43) = 3^(j+1) := by
  have hz := order_of_iterated_root (d := 3) (by decide) (by decide : 3 ∣ 129)
    j z (order_129_of_pentanomial h)
  refine ⟨hz, ?_⟩
  have hd : 43 ∣ orderOf z := hz ▸ dvd_mul_of_dvd_left (by decide : 43 ∣ 129) _
  rw [orderOf_pow_of_dvd (by decide) hd, hz, show 129 = 3 * 43 by decide,
    Nat.mul_right_comm, Nat.mul_div_cancel _ (by decide : 0 < 43), pow_succ']

end GF2Sparse
