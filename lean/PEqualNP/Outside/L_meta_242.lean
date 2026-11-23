import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_242 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasBinarySize n f s → PEqualNP.MetaComplexity.HasBinarySize n f (s + 1) := by
  intro n f s h
  rcases h with ⟨C, hs, hf⟩
  exact ⟨C, hs.trans (Nat.le_succ s), hf⟩
