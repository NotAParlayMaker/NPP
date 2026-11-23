import Mathlib
import PEqualNP.Defs

private theorem L301_aux (c : ℕ → Bool) : ∀ (m s : ℕ),
    (∀ i, i < m → c (s + 2 * i) = true ∨ c (s + 2 * i + 1) = true) →
    m ≤ ∑ j ∈ Finset.Ico s (s + 2 * m), (if c j = true then 1 else 0) := by
  intro m
  induction m with
  | zero =>
    intro s _
    exact Nat.zero_le _
  | succ m ih =>
    intro s h
    have e : s + 2 * (m + 1) = (s + 2 * m + 1) + 1 := by ring
    rw [e, Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega)]
    have h1 := ih s (fun i hi => h i (by omega))
    rcases h m (by omega) with h2 | h2
    · rw [if_pos h2]
      omega
    · rw [if_pos h2]
      omega

theorem PEqualNP.Outside.L_meta_301 : ∀ (k : ℕ) (c : ℕ → Bool), (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) → k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k c h
  have hI : Finset.Icc 1 (2 * k) = Finset.Ico 1 (1 + 2 * k) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [Finset.card_filter, hI]
  by_cases hends : c 0 = false ∧ c (2 * k + 1) = false
  · rw [if_pos hends]
    obtain ⟨h0, h1⟩ := hends
    cases k with
    | zero =>
      rcases h 0 (by omega) with h2 | h2
      · rw [h0] at h2
        exact absurd h2 (by decide)
      · rw [h1] at h2
        exact absurd h2 (by decide)
    | succ k =>
      have c1 : c 1 = true := by
        rcases h 0 (by omega) with h2 | h2
        · rw [h0] at h2
          exact absurd h2 (by decide)
        · exact h2
      have e3 : 2 * (k + 1) + 1 = 1 + 1 + 2 * k + 1 := by ring
      rw [e3] at h1
      have c2 : c (1 + 1 + 2 * k) = true := by
        rcases h (1 + 1 + 2 * k) (by omega) with h2 | h2
        · exact h2
        · rw [h1] at h2
          exact absurd h2 (by decide)
      have e : 1 + 2 * (k + 1) = (1 + 1 + 2 * k) + 1 := by ring
      rw [e, Finset.sum_Ico_succ_top (by omega), Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have hs := L301_aux c k (1 + 1) (fun i hi => h (1 + 1 + 2 * i) (by omega))
      rw [if_pos c1, if_pos c2]
      omega
  · rw [if_neg hends, Nat.add_zero]
    exact L301_aux c k 1 (fun i hi => h (1 + 2 * i) (by omega))
