import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4779 : ∀ (x1 : List (ℕ × ℕ)) (x2 : (Fin (14 : ℕ) → Bool) → Bool), ((0 : ℕ), (7 : ℕ)) ∈ x1 → (∀ (x4 x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x4 x6 = Bool.true → x5 x6 = Bool.true) → x2 x4 = Bool.true → x2 x5 = Bool.true) → (∀ (x5 : Fin (14 : ℕ) → Bool), (¬∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ x1 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (∀ (x7 : Fin (14 : ℕ)), x5 x7 = Bool.false → ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x1 ∧ Function.update x5 x7 Bool.true x9 = Bool.true ∧ Function.update x5 x7 Bool.true x10 = Bool.true) → x5 (0 : Fin (14 : ℕ)) = Bool.false ∨ x5 (7 : Fin (14 : ℕ)) = Bool.false → x2 x5 ≠ Bool.true) → ∀ (x6 : Fin (14 : ℕ) → Bool), x2 x6 = Bool.true → ∃ (x8 : Fin (14 : ℕ)) (x9 : Fin (14 : ℕ)), (↑x8, ↑x9) ∈ x1 ∧ x6 x8 = Bool.true ∧ x6 x9 = Bool.true := by
  intro E f h07 hmono hmax x hfx
  by_contra hno
  obtain ⟨M, hxM, hMmax⟩ := Finite.exists_le_maximal
    (p := fun y : Fin 14 → Bool => ¬ ∃ (u : Fin 14) (v : Fin 14), (u.1, v.1) ∈ E ∧ y u = true ∧ y v = true) hno
  have hMi := hMmax.1
  have hxM' : ∀ t, x t = true → M t = true := by
    intro t ht
    have := hxM t
    rw [Bool.le_iff_imp] at this
    exact this ht
  have hfM : f M = true := hmono x M hxM' hfx
  apply hmax M hMi ?_ ?_ hfM
  · intro t ht
    by_contra hno2
    have hle : M ≤ Function.update M t true := by
      intro s
      by_cases e : s = t
      · rw [e, Function.update_self, ht]; exact Bool.false_le _
      · rw [Function.update_of_ne e]
    have := hMmax.2 hno2 hle t
    rw [Function.update_self, ht, Bool.le_iff_imp] at this
    exact absurd (this rfl) (by decide)
  · by_contra hboth
    rw [not_or] at hboth
    have h0 : M 0 = true := by
      cases h : M 0 with
      | true => rfl
      | false => exact absurd h hboth.1
    have h7 : M 7 = true := by
      cases h : M 7 with
      | true => rfl
      | false => exact absurd h hboth.2
    exact hMi ⟨0, 7, h07, h0, h7⟩
