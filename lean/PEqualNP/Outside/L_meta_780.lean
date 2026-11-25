import Mathlib.Data.Nat.Basic

theorem PEqualNP.Outside.L_meta_780 :
    ∀ (n : ℕ) (A B H T : (Fin n → Bool) → Bool),
      ((∀ x : Fin n → Bool, (A x || (B x && !H x)) = T x) ↔
        ((∀ x : Fin n → Bool, H x = true → A x = T x) ∧
          (∀ x : Fin n → Bool, H x = false → (A x || B x) = T x))) ∧
      ((∀ x : Fin n → Bool, (A x || (B x && !H x)) = T x) →
        ∀ x : Fin n → Bool, A x = true → T x = true) := by
  intro n A B H T
  constructor
  · constructor
    · intro h
      constructor
      · intro x hx
        have hx' := h x
        simp [hx] at hx'
        exact hx'
      · intro x hx
        have hx' := h x
        simp [hx] at hx'
        exact hx'
    · intro h x
      have hA := h.1 x
      have hB := h.2 x
      by_cases hx : H x = true
      · simp [hx]
        exact hA hx
      · have hx' : H x = false := by simpa using hx
        simp [hx']
        exact hB hx'
  · intro h x hx
    have hx' := h x
    simp [hx] at hx'
    exact hx'
