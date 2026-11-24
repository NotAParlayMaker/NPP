import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4689

private lemma below_endpoint (n a b c : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hs : a + b ≤ n + 1)
    (hn : n ≤ 4511) (hc : 24 * n + 1 ≤ c)
    (h₁ : c * c ≤ b * (a * (a - 1) + c))
    (h₂ : c * c ≤ a * (b * (b - 1) + c)) : False := by
  have hn₀ : 0 ≤ n := by omega
  have hc₀ : 0 ≤ c := by omega
  have hp : 4 * (a * b) ≤ (n + 1) ^ 2 := by
    nlinarith only [sq_nonneg (a - b),
      mul_nonneg (show 0 ≤ n + 1 - (a + b) by omega)
        (show 0 ≤ n + 1 + (a + b) by omega)]
  have hprod : (4 * (a * b)) * (a + b - 2) ≤ (n + 1) ^ 2 * (n - 1) :=
    mul_le_mul hp (by omega) (by omega) (sq_nonneg (n + 1))
  have hsum : (a + b) * c ≤ (n + 1) * c := mul_le_mul_of_nonneg_right hs hc₀
  have hu : 8 * c ^ 2 ≤ (n + 1) ^ 2 * (n - 1) + 4 * (n + 1) * c := by
    linarith only [h₁, h₂, hprod, hsum]
  have hdiff := mul_nonneg (show 0 ≤ c - (24 * n + 1) by omega)
    (show 0 ≤ 8 * (c + (24 * n + 1)) - 4 * (n + 1) by omega)
  have hgap := mul_nonneg (sq_nonneg n) (show 0 ≤ 4511 - n by omega)
  linarith only [hu, hdiff, hgap, hn₀]

private lemma at_endpoint (a b c : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hs : a + b ≤ 4513)
    (hc : 108289 ≤ c) (hp : c ≤ a * b)
    (hq : c * c ≤ b * (a * (a - 1) + c)) : False := by
  have ha' : a ≤ 2256 := by omega
  have hpad : b ≤ 4513 - a := by omega
  have hp' : c ≤ a * (4513 - a) :=
    hp.trans (mul_le_mul_of_nonneg_left hpad (by omega))
  have ht : 0 ≤ a * (a - 1) + c := by
    have := mul_nonneg (show 0 ≤ a by omega) (show 0 ≤ a - 1 by omega)
    omega
  have hq' := hq.trans (mul_le_mul_of_nonneg_right hpad ht)
  have hfactor : 0 ≤ 2257 * (2256 + a - 1) - a * (a - 1) - c := by
    have := mul_nonneg (show (0 : ℤ) ≤ 2255 by norm_num) (show 0 ≤ 2257 - a by omega)
    linarith only [hp', this]
  have hbal := mul_nonneg (show 0 ≤ 2256 - a by omega) hfactor
  have hdiff := mul_nonneg (show 0 ≤ c - 108289 by omega) (show 0 ≤ c + 108289 - 2257 by omega)
  linarith only [hq', hbal, hdiff]

end PEqualNP.Outside.L_meta_4689

theorem PEqualNP.Outside.L_meta_4689 :
    ∀ (x1 x2 x3 x4 : ℕ), x1 ≤ (4512 : ℕ) → x2 + x3 ≤ x1 + (1 : ℕ) →
      x4 ≤ x2 * x3 → x4 * x4 ≤ x3 * (x2 * (x2 - (1 : ℕ)) + x4) →
      x4 * x4 ≤ x2 * (x3 * (x3 - (1 : ℕ)) + x4) → x4 ≤ (24 : ℕ) * x1 := by
  intro x1 x2 x3 x4 hn hs hp h₁ h₂
  by_cases ha : x2 = 0
  · simp [ha] at hp
    omega
  by_cases hb : x3 = 0
  · simp [hb] at hp
    omega
  by_contra hc
  have ha' : 1 ≤ x2 := by omega
  have hb' : 1 ≤ x3 := by omega
  zify [ha', hb'] at hn hs hp h₁ h₂ hc
  have haZ : (1 : ℤ) ≤ x2 := by exact_mod_cast ha'
  have hbZ : (1 : ℤ) ≤ x3 := by exact_mod_cast hb'
  by_cases h : (x1 : ℤ) ≤ 4511
  · exact PEqualNP.Outside.L_meta_4689.below_endpoint _ _ _ _ haZ hbZ hs h (by omega) h₁ h₂
  · have hs' : (x2 : ℤ) + x3 ≤ 4513 := by omega
    have hc' : (108289 : ℤ) ≤ x4 := by omega
    rcases le_total (x2 : ℤ) x3 with hab | hba
    · exact PEqualNP.Outside.L_meta_4689.at_endpoint _ _ _ haZ hab hs' hc' hp h₁
    · exact PEqualNP.Outside.L_meta_4689.at_endpoint _ _ _ hbZ hba (by omega) hc'
        (by simpa only [mul_comm (x3 : ℤ) x2] using hp) h₂
