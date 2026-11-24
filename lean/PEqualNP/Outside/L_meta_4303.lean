import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4303 : ∀ (x1 x2 : Type) (x3 x4 x5 : ℕ) (x6 : ℕ → Set (x1 × x2)),   have x7 : (ℕ → Set (x1 × x2)) → x1 × x2 → Prop := fun (x7 : ℕ → Set (x1 × x2)) (x8 : x1 × x2) => ∃ x9 < x4, x7 (x3 + x9) ⊆ x7 x5 ∧ x8 ∈ x7 (x3 + x9) ∧ ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x3 + x9 ∧ x7 (x3 + x9) = x7 x10 ∩ x7 x11 ∧ ∃ (x12 : Set x1) (x13 : Set x2), x7 x10 = x12 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x13;   (0 : ℕ) < x3 → (∀ x9 < x3, x6 x9 ≠ ∅) → x6 x5 ≠ ∅ → ¬x6 (0 : ℕ) ⊆ x6 x5 → (∀ x12 < x4, ∃ (x14 : ℕ) (x15 : ℕ), Max.max x14 x15 < x3 + x12 ∧ x6 (x3 + x12) ∈ [x6 x14 ∪ x6 x15, x6 x14, ∅, x6 x14 ∩ x6 x15]) → ∃ (x13 : ℕ → Set (x1 × x2)), (∀ x14 < x3, x13 x14 = x6 x14) ∧ x13 x5 = x6 x5 ∧ (∀ (x14 : ℕ), x13 x14 ≠ ∅) ∧ (∀ x14 < x4, ∃ (x16 : ℕ) (x17 : ℕ), Max.max x16 x17 < x3 + x14 ∧ (x13 (x3 + x14) = x13 x16 ∪ x13 x17 ∨ x13 (x3 + x14) = x13 x16 ∩ x13 x17)) ∧ ∀ (x14 : x1 × x2), x7 x13 x14 → x7 x6 x14 := by
  intro X Y n s out f P hn hin hout h0 hg
  classical
  have h0ne : f 0 ≠ ∅ := hin 0 hn
  refine ⟨fun w => if f w = ∅ then f 0 else f w, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [hin i hi]
  · simp [hout]
  · intro w
    dsimp only
    split_ifs with h
    · exact h0ne
    · exact h
  · intro j hj
    obtain ⟨a, b, hab, hfj⟩ := hg j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfj
    by_cases he : f (n + j) = ∅
    · refine ⟨0, 0, by simp; omega, Or.inl ?_⟩
      simp [he, h0ne]
    · rcases hfj with h | h | h | h
      · by_cases ha : f a = ∅
        · by_cases hb : f b = ∅
          · exact absurd (by rw [h, ha, hb]; simp) he
          · refine ⟨b, b, by omega, Or.inl ?_⟩
            simp [he, hb, h, ha]
        · by_cases hb : f b = ∅
          · refine ⟨a, a, by omega, Or.inl ?_⟩
            simp [he, ha, h, hb]
          · refine ⟨a, b, hab, Or.inl ?_⟩
            simp [he, ha, hb, h]
      · have ha : f a ≠ ∅ := h ▸ he
        refine ⟨a, a, by omega, Or.inl ?_⟩
        simp [he, ha, h]
      · exact absurd h he
      · have ha : f a ≠ ∅ := fun e => he (by rw [h, e]; simp)
        have hb : f b ≠ ∅ := fun e => he (by rw [h, e]; simp)
        have hab' : f a ∩ f b ≠ ∅ := h ▸ he
        refine ⟨a, b, hab, Or.inr ?_⟩
        simp [he, ha, hb, h, hab']
  · intro p hp
    simp only [P] at hp ⊢
    obtain ⟨j, hj, hsub, hpj, a, b, hab, hand, A, B, hA, hB⟩ := hp
    have hgo : (if f out = ∅ then f 0 else f out) = f out := by simp [hout]
    rw [hgo] at hsub
    have hne : f (n + j) ≠ ∅ := by
      intro e
      rw [if_pos e] at hsub
      exact h0 hsub
    rw [if_neg hne] at hsub hpj hand
    refine ⟨j, hj, hsub, hpj, if f a = ∅ then 0 else a, if f b = ∅ then 0 else b, ?_, ?_,
      A, B, ?_, ?_⟩
    · split_ifs <;> simp <;> omega
    · rw [hand]
      split_ifs <;> rfl
    · rw [← hA]
      split_ifs <;> rfl
    · rw [← hB]
      split_ifs <;> rfl
