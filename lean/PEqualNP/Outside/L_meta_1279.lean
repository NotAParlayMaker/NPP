import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1279 : ∀ (n : ℕ) (marked : Finset ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (D D' : ℕ), PEqualNP.CircuitLowerBounds.HasLineDegree n marked C D → D ≤ D' → PEqualNP.CircuitLowerBounds.HasLineDegree n marked C D' := by
  intro n marked C D D' h hD
  exact le_trans h hD
