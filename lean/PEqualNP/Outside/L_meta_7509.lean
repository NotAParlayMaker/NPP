import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7509 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),   let x5 : Type := (Fin x1 → Bool) × (Fin x1 → Bool);   x3 < x1 + x1 + x2 → (∀ (x7 : Fin x1), x4 ↑x7 = {x8 : x5 | x8.1 x7 = Bool.true} ∧ x4 (x1 + ↑x7) = {x8 : x5 | x8.2 x7 = Bool.true}) → (∀ x8 < x2, ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x1 + x1 + x8 ∧ x4 (x1 + x1 + x8) ∈ [x4 x10 ∪ x4 x11, x4 x10, ∅, x4 x10 ∩ x4 x11]) → (∃ (x9 : x5), x9 ∈ x4 x3) → ∃ x10 ≤ x2, ∃ x11 < x1 + x1 + x10, ∃ (x12 : ℕ → Set x5), (∀ (x13 : Fin x1), x12 ↑x13 = {x14 : x5 | x14.1 x13 = Bool.true} ∧ x12 (x1 + ↑x13) = {x14 : x5 | x14.2 x13 = Bool.true}) ∧ (∀ x13 < x10, ∃ x15 < x1 + x1 + x13, ∃ x16 < x1 + x1 + x13, x12 (x1 + x1 + x13) = x12 x15 ∪ x12 x16 ∨ x12 (x1 + x1 + x13) = x12 x15 ∩ x12 x16) ∧ ∀ (x13 : x5), x13 ∈ x12 x11 ↔ x13 ∈ x4 x3 := by
  intro x1 x2 x3 x4 x5 h3 hin hg hne
  have hx1 : 0 < x1 := by
    rcases Nat.eq_zero_or_pos x1 with h | h
    · subst h
      rcases Nat.eq_zero_or_pos x2 with h2 | h2
      · omega
      · obtain ⟨a, b, hab, -⟩ := hg 0 h2
        have := le_max_left a b
        omega
    · exact h
  classical
  obtain ⟨x12, hx12⟩ : ∃ x12 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool)), ∀ w, x12 w = if 2 * x1 ≤ w ∧ x4 w = ∅ then x4 0 else x4 w := ⟨_, fun _ => rfl⟩
  have key1 : ∀ w, x4 w ≠ ∅ → x12 w = x4 w := by
    intro w hw
    rw [hx12]
    simp [hw]
  have key2 : ∀ w, w < 2 * x1 → x12 w = x4 w := by
    intro w hw
    rw [hx12, if_neg]
    exact fun h => absurd h.1 (by omega)
  have key3 : ∀ w, 2 * x1 ≤ w → x4 w = ∅ → x12 w = x12 0 := by
    intro w h1 h2
    rw [hx12 w, if_pos ⟨h1, h2⟩, key2 0 (by omega)]
  refine ⟨x2, le_rfl, x3, h3, x12, ?_, ?_, ?_⟩
  · intro i
    have hi := i.2
    have h1 := key2 i (by omega)
    have h2 := key2 (x1 + i) (by omega)
    rw [h1, h2]
    exact hin i
  · intro w hw
    obtain ⟨a, b, hab, hmem⟩ := hg w hw
    have ha : a < x1 + x1 + w := lt_of_le_of_lt (le_max_left a b) hab
    have hb : b < x1 + x1 + w := lt_of_le_of_lt (le_max_right a b) hab
    by_cases he : x4 (x1 + x1 + w) = ∅
    · refine ⟨0, by omega, 0, by omega, Or.inl ?_⟩
      rw [key3 _ (by omega) he, Set.union_self]
    · rw [key1 _ he]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
      rcases hmem with h | h | h | h
      · by_cases ea : x4 a = ∅
        · have hbn : x4 b ≠ ∅ := by
            intro eb
            apply he
            rw [h, ea, eb]
            simp
          refine ⟨b, hb, b, hb, Or.inl ?_⟩
          rw [key1 b hbn, h, ea]
          simp
        · by_cases eb : x4 b = ∅
          · refine ⟨a, ha, a, ha, Or.inl ?_⟩
            rw [key1 a ea, h, eb]
            simp
          · refine ⟨a, ha, b, hb, Or.inl ?_⟩
            rw [key1 a ea, key1 b eb, h]
      · have ea : x4 a ≠ ∅ := h ▸ he
        refine ⟨a, ha, a, ha, Or.inl ?_⟩
        rw [key1 a ea, h]
        simp
      · exact absurd h he
      · have ea : x4 a ≠ ∅ := by
          intro ea
          apply he
          rw [h, ea]
          simp
        have eb : x4 b ≠ ∅ := by
          intro eb
          apply he
          rw [h, eb]
          simp
        refine ⟨a, ha, b, hb, Or.inr ?_⟩
        rw [key1 a ea, key1 b eb, h]
  · intro p
    have hn : x4 x3 ≠ ∅ := Set.nonempty_iff_ne_empty.mp hne
    rw [key1 x3 hn]
