import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8061 : ∀ (x1 x2 x3 : ℕ) (x4 x5 : ℕ → ℕ) (x6 x7 x8 : ℕ → Bool),   x3 < x1 →     (∀ x10 < x2, x4 x10 < x1 + x10 ∧ x5 x10 < x1 + x10) →       (∀ x11 < x1, x8 x11 = Decidable.decide (x11 = x3)) →         (∀ x12 < x2, x8 (x1 + x12) = (x8 (x4 x12) && x6 x12 || x8 (x5 x12) && x7 x12)) →           have x13 : ℕ → ℕ → Prop := fun (x13 x14 : ℕ) => ∃ x15 < x2, x14 = x1 + x15 ∧ (x13 = x4 x15 ∧ x6 x15 = Bool.true ∨ x13 = x5 x15 ∧ x7 x15 = Bool.true);           ∀ x14 < x1 + x2, x8 x14 = Bool.true ↔ Relation.ReflTransGen x13 x3 x14 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 h3 hg hin hgate x13 x14
  induction x14 using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < x1
    · rw [hin n hlt]
      constructor
      · intro h
        have : n = x3 := by simpa using h
        subst this
        exact Relation.ReflTransGen.refl
      · intro h
        rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, _, hb⟩
        · simp [h]
        · obtain ⟨k, _, hk, _⟩ := hb
          omega
    · obtain ⟨k, rfl⟩ : ∃ k, n = x1 + k := ⟨n - x1, by omega⟩
      have hk : k < x2 := by omega
      have hne : x1 + k ≠ x3 := by omega
      obtain ⟨ha, hb⟩ := hg k hk
      have iha := ih (x4 k) ha (by omega)
      have ihb := ih (x5 k) hb (by omega)
      rw [hgate k hk]
      constructor
      · intro h
        simp only [Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Relation.ReflTransGen.tail (iha.mp h1) ⟨k, hk, rfl, Or.inl ⟨rfl, h2⟩⟩
        · exact Relation.ReflTransGen.tail (ihb.mp h1) ⟨k, hk, rfl, Or.inr ⟨rfl, h2⟩⟩
      · intro h
        rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, hr, j, hj, hjk, hc⟩
        · exact absurd h hne
        · have : j = k := by omega
          subst this
          simp only [Bool.or_eq_true, Bool.and_eq_true]
          rcases hc with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
          · exact Or.inl ⟨iha.mpr hr, h2⟩
          · exact Or.inr ⟨ihb.mpr hr, h2⟩
