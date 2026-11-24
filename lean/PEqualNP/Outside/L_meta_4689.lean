import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4689.poly (a d : ℤ) (ha : 1 ≤ a) (hd : 0 ≤ d) (h : 2 * a + d ≤ 4513) :
    a * (a + d) * (a - 1) < (48 * a + 24 * d - 23) * (47 * a + 23 * d - 23) := by
  have ha2 : a ≤ 2256 := by omega
  rcases le_or_gt a 2233 with h1 | h1
  · have e1 : 0 ≤ (a - 1) * (2256 - a) := mul_nonneg (by omega) (by omega)
    have e2 : 0 ≤ a * ((a - 1) * (2256 - a)) := mul_nonneg (by omega) e1
    have e3 : 0 ≤ d * (a * (2233 - a)) := mul_nonneg hd (mul_nonneg (by omega) (by omega))
    have e4 : 0 ≤ (d - 1) * (552 * d - 529) + 0 := by
      rcases eq_or_lt_of_le hd with h0 | h0
      · rw [← h0]; norm_num
      · have : 0 ≤ (d - 1) * (552 * d - 529) := mul_nonneg (by omega) (by omega)
        omega
    nlinarith
  · have hd2 : d ≤ 4513 - 2 * a := by omega
    have hsq : 0 ≤ d * d := mul_nonneg hd hd
    interval_cases a <;> nlinarith

theorem PEqualNP.Outside.L_meta_4689.core (a b E s : ℕ) (hs : s ≤ 4512) (hab : a + b ≤ s + 1) (hle : a ≤ b)
    (h0 : E ≤ a * b) (h1 : E * E ≤ b * (a * (a - 1) + E)) : E ≤ 24 * s := by
  by_contra hcon
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h
    simp at h0
    omega
  · obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [Nat.add_sub_cancel] at h1
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hp := PEqualNP.Outside.L_meta_4689.poly (a + 1 : ℤ) (d : ℤ) (by omega) (by omega) (by omega)
    have h1' : (E : ℤ) * E ≤ (a + 1 + d) * ((a + 1) * a + E) := by exact_mod_cast h1
    have hE : (48 * (a + 1) + 24 * d - 23 : ℤ) ≤ E := by omega
    have hmul : 0 ≤ ((E : ℤ) - (48 * (a + 1) + 24 * d - 23)) *
        (E + (48 * (a + 1) + 24 * d - 23) - (a + 1 + d)) := mul_nonneg (by omega) (by omega)
    nlinarith

theorem PEqualNP.Outside.L_meta_4689 : ∀ (x1 x2 x3 x4 : ℕ), x1 ≤ (4512 : ℕ) → x2 + x3 ≤ x1 + (1 : ℕ) → x4 ≤ x2 * x3 → x4 * x4 ≤ x3 * (x2 * (x2 - (1 : ℕ)) + x4) → x4 * x4 ≤ x2 * (x3 * (x3 - (1 : ℕ)) + x4) → x4 ≤ (24 : ℕ) * x1 := by
  intro s a b E hs hab h0 h1 h2
  rcases le_total a b with h | h
  · exact PEqualNP.Outside.L_meta_4689.core a b E s hs hab h h0 h1
  · exact PEqualNP.Outside.L_meta_4689.core b a E s hs (by omega) h (by rw [Nat.mul_comm]; exact h0) h2
