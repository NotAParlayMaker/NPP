import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_242 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasBinarySize n f s → PEqualNP.MetaComplexity.HasBinarySize n f (s + 1) := by
  rintro n f s ⟨C, hs, h⟩
  exact ⟨C, Nat.le_succ_of_le hs, h⟩
