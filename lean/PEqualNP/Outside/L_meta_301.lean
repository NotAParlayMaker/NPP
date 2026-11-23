import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_301 :
    ∀ (k : ℕ) (c : ℕ → Bool), (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) → k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k c hc
  induction k with
  | zero =>
    have h0 := hc 0 (by omega)
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [Finset.Icc_eq_empty (by norm_num), Finset.filter_empty, Finset.card_empty]
    split_ifs with h
    · exfalso
      rcases h with ⟨ha, hb⟩
      rcases h0 with h0 | h0
      · rw [ha] at h0; exact Bool.false_ne_true h0
      · rw [hb] at h0; exact Bool.false_ne_true h0
    · exact le_rfl
  | succ k ih =>
    have ih' := ih (fun j hj => hc j (by omega))
    have hcard : ((Finset.Icc 1 (2 * (k + 1))).filter (fun j => c j = true)).card =
        ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card +
          (if c (2 * k + 1) = true then 1 else 0) + (if c (2 * k + 1 + 1) = true then 1 else 0) := by
      rw [Finset.card_filter, Finset.card_filter, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
        Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    rw [hcard, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring]
    have h1 := hc (2 * k + 1) (by omega)
    have h2 := hc (2 * k + 1 + 1) (by omega)
    have h0 := hc 0 (by omega)
    cases hA : c 0 <;> cases hB : c (2 * k + 1) <;> cases hC : c (2 * k + 1 + 1) <;> cases hD : c (2 * k + 1 + 1 + 1) <;>
      simp only [hA, hB, hC, hD, Bool.false_eq_true, Bool.true_eq_false, and_self, and_true, and_false,
        ite_true, ite_false, or_false, false_or, or_self] at ih' h1 h2 h0 ⊢ <;> omega
