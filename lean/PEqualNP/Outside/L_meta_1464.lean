import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1464 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    3 ≤ (S i0).card → (∀ i : Fin m, i ≠ i0 → (S i ∩ S i0).card ≤ 1) →
    ∃ (r : Fin n → Fin n → Prop) (f : Fin m → Fin n), (∀ a b : Fin n, r a b → ¬ r b a) ∧
      ∀ i : Fin m, i ≠ i0 → f i ∈ S i0 ∧ f i ∉ S i ∧ ∀ y ∈ S i ∩ S i0, r (f i) y := by
  intro n m S i0 h3 hI
  classical
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < (S i0).card)
  obtain ⟨g, hg⟩ : ∃ g : Fin n → Fin n, g = fun y => if y = a then c else if y = b then a else if y = c then b else a := ⟨_, rfl⟩
  have gmem : ∀ y, g y ∈ S i0 := by
    intro y
    rw [hg]
    simp only
    split_ifs <;> assumption
  have gne : ∀ y, g y ≠ y := by
    intro y
    rw [hg]
    simp only
    split_ifs with h1 h2 h3
    · rw [h1]; exact fun e => hac e.symm
    · rw [h2]; exact hab
    · rw [h3]; exact hbc
    · exact fun e => h1 e.symm
  have gg : ∀ y, g (g y) ≠ y := by
    intro y
    rw [hg]
    simp only
    by_cases h1 : y = a
    · subst h1
      simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
    · by_cases h2 : y = b
      · subst h2
        simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
      · by_cases h3 : y = c
        · subst h3
          simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
        · simp [h1, h2, h3, hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
          exact fun e => h3 e.symm
  refine ⟨fun x y => x = g y, fun i => if h : (S i ∩ S i0).Nonempty then g h.choose else a, ?_, ?_⟩
  · intro x y hxy hyx
    exact gg y (by rw [← hxy]; exact hyx.symm)
  · intro i hi
    by_cases h : (S i ∩ S i0).Nonempty
    · simp only [dif_pos h]
      have hy := h.choose_spec
      have uniq : ∀ z ∈ S i ∩ S i0, z = h.choose := fun z hz =>
        Finset.card_le_one.mp (hI i hi) z hz _ hy
      refine ⟨gmem _, ?_, ?_⟩
      · intro hin
        exact gne _ (uniq _ (Finset.mem_inter.mpr ⟨hin, gmem _⟩))
      · intro z hz
        rw [uniq z hz]
    · simp only [dif_neg h]
      refine ⟨ha, ?_, ?_⟩
      · intro hin
        exact h ⟨a, Finset.mem_inter.mpr ⟨hin, ha⟩⟩
      · intro z hz
        exact absurd ⟨z, hz⟩ h
