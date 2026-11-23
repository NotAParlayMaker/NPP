import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_242 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
      HasBinarySize n f s → HasBinarySize n f (s + 1) := by
  intro n f s h
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, by omega, hf⟩
