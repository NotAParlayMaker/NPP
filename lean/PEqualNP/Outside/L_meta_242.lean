import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_242 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasBinarySize n f s → PEqualNP.MetaComplexity.HasBinarySize n f (s + 1) := by
  intro n f s h
  exact Exists.imp (fun C hC => And.intro (Nat.le_trans hC.left (Nat.le_succ s)) hC.right) h
