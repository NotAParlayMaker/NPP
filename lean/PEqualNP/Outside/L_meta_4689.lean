import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4689

lemma main_wlog (x1 x2 x3 x4 : ℕ)
    (hx1 : x1 ≤ 4512) (hsum : x2 + x3 ≤ x1 + 1) (hprod : x4 ≤ x2 * x3)
    (h1 : x4 * x4 ≤ x3 * (x2 * (x2 - 1) + x4))
    (hle : x2 ≤ x3) : x4 ≤ 24 * x1 := by
  by_contra hlt
  have hlt' : 24 * x1 < x4 := Nat.lt_of_not_ge hlt
  have hx2_gt : 24 < x2 := by
    by_contra h24
    have h1' : x2 ≤ 24 := Nat.le_of_not_lt h24
    rcases Nat.eq_zero_or_pos x2 with rfl | hpos
    · simp at hprod
      omega
    · have : x3 ≤ x1 := by omega
      have : x2 * x3 ≤ 24 * x1 := Nat.mul_le_mul h1' this
      omega
  have hx1_ge : 49 ≤ x1 := by omega
  set e : ℤ := 24 * (x1 : ℤ) + 1
  have h1Z : (x4 : ℤ) * (x4 : ℤ) ≤ (x3 : ℤ) * ((x2 : ℤ) * ((x2 : ℤ) - 1) + (x4 : ℤ)) := by
    have hsub : ((x2 - 1 : ℕ) : ℤ) = (x2 : ℤ) - 1 := by omega
    have hcast : ((x4 * x4 : ℕ) : ℤ) ≤ ((x3 * (x2 * (x2 - 1) + x4) : ℕ) : ℤ) := Int.ofNat_le.mpr h1
    push_cast at hcast
    rw [hsub] at hcast
    exact hcast
  have h1eZ : e * e ≤ (x3 : ℤ) * ((x2 : ℤ) * ((x2 : ℤ) - 1) + e) := by
    have hge : e ≤ (x4 : ℤ) := by omega
    have hsumpos : (x3 : ℤ) ≤ (x4 : ℤ) + e := by omega
    nlinarith
  by_cases hs4300 : x2 + x3 ≤ 4300
  · set s : ℤ := (x2 : ℤ) + (x3 : ℤ)
    have hbound1 : 8 * (x3 : ℤ) * ((x2 : ℤ) * ((x2 : ℤ) - 1)) ≤ s * s * (s - 2) := by
      have hsq : 4 * (x2 : ℤ) * (x3 : ℤ) ≤ s * s := by nlinarith
      have hlin : 2 * ((x2 : ℤ) - 1) ≤ s - 2 := by omega
      have hnn1 : 0 ≤ 2 * ((x2 : ℤ) - 1) := by omega
      have hnn2 : 0 ≤ s * s := by nlinarith
      nlinarith
    have hbound2 : 8 * (x3 : ℤ) * e ≤ 8 * s * e := by nlinarith
    have hsmall : s * s * (s - 2) + 8 * s * e < 8 * e * e := by
      have hs1 : s ≤ (x1 : ℤ) + 1 := by omega
      have hs2 : s - 2 ≤ 4298 := by omega
      have hss : s * s ≤ ((x1 : ℤ) + 1) * ((x1 : ℤ) + 1) := by nlinarith
      have hcub : s * s * (s - 2) ≤ ((x1 : ℤ) + 1) * ((x1 : ℤ) + 1) * 4298 := by nlinarith
      have hlin : 8 * s * e ≤ 8 * ((x1 : ℤ) + 1) * (24 * (x1 : ℤ) + 1) := by nlinarith
      nlinarith
    linarith
  · have hs4301 : 4301 ≤ x2 + x3 := by omega
    by_cases hx2_55 : x2 < 55
    · have : (x2 : ℤ) * ((x2 : ℤ) - 1) ≤ 54 * 53 := by nlinarith
      have hx1_4300 : 4300 ≤ (x1 : ℤ) := by omega
      have hx3_4513 : (x3 : ℤ) ≤ 4513 := by omega
      nlinarith
    · have hx2_ge55 : 55 ≤ x2 := by omega
      by_cases htopcase : x1 = 4512 ∧ x2 + x3 = 4513
      · rcases htopcase with ⟨rfl, hs4513⟩
        have heval : e = 108289 := by omega
        set u : ℤ := 2256 - (x2 : ℤ)
        have hu0 : 0 ≤ u := by omega
        have hu1 : u ≤ 2256 := by omega
        have hx2u : (x2 : ℤ) = 2256 - u := by omega
        have hx3u : (x3 : ℤ) = 2257 + u := by omega
        have hdiff : e * e - (x3 : ℤ) * ((x2 : ℤ) * ((x2 : ℤ) - 1) + e) =
            108288 + u * (4985758 + u * (2254 - u)) := by
          rw [heval, hx2u, hx3u]
          ring
        have hinner : 0 ≤ 4985758 + u * (2254 - u) := by nlinarith
        have hprod0 : 0 ≤ u * (4985758 + u * (2254 - u)) := mul_nonneg hu0 hinner
        linarith
      · set s : ℤ := (x2 : ℤ) + (x3 : ℤ)
        set d : ℤ := (x3 : ℤ) - (x2 : ℤ)
        have hd0 : 0 ≤ d := by omega
        have hid : 8 * (x3 : ℤ) * ((x2 : ℤ) * ((x2 : ℤ) - 1) + e) =
            s * s * (s - 2) + 4 * s * e - d * ((s - d) * (s + d) + d * (s - 2) - 4 * e) := by
          dsimp [s, d]
          ring
        have hpos : 0 ≤ (s - d) * (s + d) + d * (s - 2) - 4 * e := by
          have hsd1 : 110 ≤ s - d := by omega
          have hsd2 : 4301 ≤ s + d := by omega
          have hs2 : 0 ≤ s - 2 := by omega
          have heZ : e ≤ 108289 := by omega
          have hm1 : 110 * 4301 ≤ (s - d) * (s + d) := mul_le_mul hsd1 hsd2 (by norm_num) (by omega)
          have hm2 : 0 ≤ d * (s - 2) := mul_nonneg hd0 hs2
          linarith only [hm1, hm2, heZ]
        have hdrop : d * ((s - d) * (s + d) + d * (s - 2) - 4 * e) ≥ 0 := mul_nonneg hd0 hpos
        have hlt8 : s * s * (s - 2) + 4 * s * e < 8 * e * e := by
          by_cases hx1_4512 : x1 = 4512
          · have hs4512 : s ≤ 4512 := by omega
            have heval : e = 108289 := by omega
            have hss : s * s ≤ 4512 * 4512 := mul_le_mul hs4512 hs4512 (by omega) (by norm_num)
            have hcub : s * s * (s - 2) ≤ 4512 * 4512 * 4510 := mul_le_mul hss (by omega) (by omega) (by norm_num)
            have hlin : 4 * s * e ≤ 4 * 4512 * 108289 := by rw [heval]; omega
            have hee : 8 * e * e = 8 * 108289 * 108289 := by rw [heval]
            linarith only [hcub, hlin, hee]
          · have hx1_4511 : (x1 : ℤ) ≤ 4511 := by omega
            have hx1_nn : 0 ≤ (x1 : ℤ) := by omega
            have hs_le : s ≤ (x1 : ℤ) + 1 := by omega
            have hss : s * s ≤ ((x1 : ℤ) + 1) * ((x1 : ℤ) + 1) := mul_le_mul hs_le hs_le (by omega) (by omega)
            have hcub : s * s * (s - 2) ≤ ((x1 : ℤ) + 1) * ((x1 : ℤ) + 1) * ((x1 : ℤ) - 1) :=
              mul_le_mul hss (by omega) (by omega) (mul_nonneg (by omega) (by omega))
            have hlin : 4 * s * e ≤ 4 * ((x1 : ℤ) + 1) * (24 * (x1 : ℤ) + 1) := by
              have h4 : 4 * s ≤ 4 * ((x1 : ℤ) + 1) := by omega
              have hmul : 4 * s * (24 * (x1 : ℤ) + 1) ≤ 4 * ((x1 : ℤ) + 1) * (24 * (x1 : ℤ) + 1) :=
                mul_le_mul_of_nonneg_right h4 (by omega)
              exact hmul
            have hx1_cub : (x1 : ℤ) * (x1 : ℤ) * (x1 : ℤ) ≤ 4511 * ((x1 : ℤ) * (x1 : ℤ)) := by
              have hsq : 0 ≤ (x1 : ℤ) * (x1 : ℤ) := mul_nonneg hx1_nn hx1_nn
              have := mul_le_mul_of_nonneg_right hx1_4511 hsq
              linarith only [this]
            have hcube_bound : ((x1 : ℤ) + 1) * ((x1 : ℤ) + 1) * ((x1 : ℤ) - 1) +
                4 * ((x1 : ℤ) + 1) * (24 * (x1 : ℤ) + 1) <
                8 * (24 * (x1 : ℤ) + 1) * (24 * (x1 : ℤ) + 1) := by
              have hdiff : 8 * (24 * (x1 : ℤ) + 1) * (24 * (x1 : ℤ) + 1) -
                  (((x1 : ℤ) + 1) * ((x1 : ℤ) + 1) * ((x1 : ℤ) - 1) +
                   4 * ((x1 : ℤ) + 1) * (24 * (x1 : ℤ) + 1)) =
                  (4511 * ((x1 : ℤ) * (x1 : ℤ)) - (x1 : ℤ) * (x1 : ℤ) * (x1 : ℤ)) +
                  285 * (x1 : ℤ) + 5 := by ring
              linarith only [hdiff, hx1_cub, hx1_nn]
            have hee : 8 * e * e = 8 * (24 * (x1 : ℤ) + 1) * (24 * (x1 : ℤ) + 1) := by
              dsimp [e]
            linarith only [hcub, hlin, hcube_bound, hee]
        linarith only [h1eZ, hid, hdrop, hlt8]

end PEqualNP.Outside.L_meta_4689

theorem PEqualNP.Outside.L_meta_4689 : ∀ (x1 x2 x3 x4 : ℕ), x1 ≤ (4512 : ℕ) → x2 + x3 ≤ x1 + (1 : ℕ) → x4 ≤ x2 * x3 → x4 * x4 ≤ x3 * (x2 * (x2 - (1 : ℕ)) + x4) → x4 * x4 ≤ x2 * (x3 * (x3 - (1 : ℕ)) + x4) → x4 ≤ (24 : ℕ) * x1 := by
  intro x1 x2 x3 x4 hx1 hsum hprod h1 h2
  rcases le_total x2 x3 with hle | hle
  · exact PEqualNP.Outside.L_meta_4689.main_wlog x1 x2 x3 x4 hx1 hsum hprod h1 hle
  · exact PEqualNP.Outside.L_meta_4689.main_wlog x1 x3 x2 x4 hx1 (by omega) (by simpa [Nat.mul_comm] using hprod) h2 hle
