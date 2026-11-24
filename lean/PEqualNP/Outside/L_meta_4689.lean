import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

namespace PEqualNP.Outside.L_meta_4689_aux

theorem q_pos (a : ℤ) (h1 : 1 ≤ a) (h2 : a ≤ 2255) :
    0 < -100 * a ^ 2 + 225652 * a - 216154 := by
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2)]

theorem key (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hs : a + b ≤ 4513) :
    a * (a - 1) * b < (24 * a + 24 * b - 23) * (24 * a + 23 * b - 23) := by
  rcases lt_or_ge a 2256 with h | h
  · have hq := q_pos a ha (by omega)
    have hb : 0 < b := by omega
    nlinarith [sq_nonneg (2349 * b - 100 * (24 * a - 23)), mul_pos hb hq, mul_pos hb hb]
  · have ha' : a = 2256 := by omega
    subst ha'
    have hb1 : 2256 ≤ b := hab
    have hb2 : b ≤ 2257 := by omega
    interval_cases b <;> norm_num

theorem half (N a b e : ℕ) (hs : a + b ≤ N + 1) (hN : N ≤ 4512) (ha : 1 ≤ a) (hab : a ≤ b)
    (h1 : e * e ≤ b * (a * (a - 1) + e)) (hc : 24 * N < e) : False := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1
  have hk := key ((c : ℤ) + 1) (b : ℤ) (by omega) (by exact_mod_cast hab) (by
    have : c + 1 + b ≤ 4513 := by omega
    exact_mod_cast this)
  have h1' : (e : ℤ) * e ≤ b * ((c + 1) * c + e) := by exact_mod_cast h1
  have hc' : 24 * ((c : ℤ) + 1 + b) - 23 ≤ e := by
    have : 24 * (c + 1 + b) ≤ e + 23 := by omega
    have h := (show ((24 * (c + 1 + b) : ℕ) : ℤ) ≤ ((e + 23 : ℕ) : ℤ) by exact_mod_cast this)
    push_cast at h
    linarith
  have hE : (b : ℤ) ≤ 24 * ((c : ℤ) + 1 + b) - 23 := by
    have : (0 : ℤ) ≤ c := by positivity
    linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hc') (show (0 : ℤ) ≤ e + (24 * ((c : ℤ) + 1 + b) - 23) - b by linarith)]

end PEqualNP.Outside.L_meta_4689_aux

theorem PEqualNP.Outside.L_meta_4689 : ∀ (x1 x2 x3 x4 : ℕ), x1 ≤ (4512 : ℕ) → x2 + x3 ≤ x1 + (1 : ℕ) → x4 ≤ x2 * x3 → x4 * x4 ≤ x3 * (x2 * (x2 - (1 : ℕ)) + x4) → x4 * x4 ≤ x2 * (x3 * (x3 - (1 : ℕ)) + x4) → x4 ≤ (24 : ℕ) * x1 := by
  intro N a b e hN hs he h1 h2
  by_contra hc0
  have hc : 24 * N < e := Nat.lt_of_not_le hc0
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    simp at he
    omega
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    simp at he
    omega
  rcases le_total a b with hab | hab
  · exact PEqualNP.Outside.L_meta_4689_aux.half N a b e hs hN ha hab h1 hc
  · exact PEqualNP.Outside.L_meta_4689_aux.half N b a e (by omega) hN hb hab h2 hc
