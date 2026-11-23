import Mathlib
import PEqualNP.Defs

-- The same circuit witnesses the larger bound, since s is at most s plus one.
theorem PEqualNP.Outside.L_meta_242 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ),
      PEqualNP.MetaComplexity.HasBinarySize n f s →
      PEqualNP.MetaComplexity.HasBinarySize n f (s + 1) := by
  intro n f s h
  obtain ⟨C, hsize, heval⟩ := h
  exact ⟨C, le_trans hsize (Nat.le_succ s), heval⟩
