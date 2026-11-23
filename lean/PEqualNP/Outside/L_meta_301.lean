import PEqualNP.Defs
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside

theorem L_meta_301 :
    ∀ (k : ℕ) (c : ℕ → Bool),
      (∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true) →
      k + (if c 0 = false ∧ c (2 * k + 1) = false then 1 else 0) ≤
        ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
  intro k
  induction k with
  | zero =>
    intro c hc
    have h0 := hc 0 (le_refl 0)
    have hnot : ¬ (c 0 = false ∧ c 1 = false) := by
      rintro ⟨h1, h2⟩
      rcases h0 with h | h <;> simp [h1, h2] at h
    simp [hnot]
  | succ k ih =>
    intro c hc
    have hc_prev : ∀ j : ℕ, j ≤ 2 * k → c j = true ∨ c (j + 1) = true :=
      fun j hj => hc j (by omega)
    have hih := ih c hc_prev
    have hsplit : Finset.Icc 1 (2 * (k + 1)) =
        Finset.Icc 1 (2 * k) ∪ {2 * k + 1, 2 * k + 2} := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      omega
    have hdisj : Disjoint (Finset.Icc 1 (2 * k)) {2 * k + 1, 2 * k + 2} := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      omega
    have hcard_eq :
        ((Finset.Icc 1 (2 * (k + 1))).filter (fun j => c j = true)).card =
          ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card +
          (({2 * k + 1, 2 * k + 2} : Finset ℕ).filter (fun j => c j = true)).card := by
      rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint]
      exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj
    have hpair_ge1 :
        1 ≤ (({2 * k + 1, 2 * k + 2} : Finset ℕ).filter (fun j => c j = true)).card := by
      rcases hc (2 * k + 1) (by omega) with h1 | h2
      · exact Finset.card_pos.mpr ⟨2 * k + 1, by simp [h1]⟩
      · exact Finset.card_pos.mpr ⟨2 * k + 2, by simp [h2]⟩
    rw [hcard_eq]
    by_cases hcond : c 0 = false ∧ c (2 * (k + 1) + 1) = false
    · rw [if_pos hcond]
      have hc_end : c (2 * k + 2) = true := by
        rcases hc (2 * k + 2) (by omega) with h | h
        · exact h
        · exfalso
          have h2 := hcond.2
          have : 2 * k + 2 + 1 = 2 * (k + 1) + 1 := by omega
          rw [this] at h
          simp [h2] at h
      cases hmid : c (2 * k + 1)
      · have hih' : k + 1 ≤ ((Finset.Icc 1 (2 * k)).filter (fun j => c j = true)).card := by
          have : c 0 = false ∧ c (2 * k + 1) = false := ⟨hcond.1, hmid⟩
          simpa [this] using hih
        omega
      · have hpair_eq2 :
            (({2 * k + 1, 2 * k + 2} : Finset ℕ).filter (fun j => c j = true)).card = 2 := by
          have hfilt :
              ({2 * k + 1, 2 * k + 2} : Finset ℕ).filter (fun j => c j = true) =
                {2 * k + 1, 2 * k + 2} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
              and_iff_left_iff_imp]
            rintro (rfl | rfl)
            · exact hmid
            · exact hc_end
          rw [hfilt, Finset.card_pair (by omega)]
        omega
    · rw [if_neg hcond]
      omega

end PEqualNP.Outside
