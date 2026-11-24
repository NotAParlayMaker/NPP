import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3218 : ∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 := by
  exact ⟨0, fun x2 => Nat.zero_le x2⟩
