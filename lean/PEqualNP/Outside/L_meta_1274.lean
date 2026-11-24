import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1274 : ∀ (n i : ℕ) (marked : Finset ℕ), i < n → ({ gates := [], output := i } : PEqualNP.CircuitLowerBounds.Circuit).lineDeg n marked = (if i ∈ marked then 1 else 0) := by
  intro n i marked hi
  simp only [PEqualNP.CircuitLowerBounds.Circuit.lineDeg,
    PEqualNP.CircuitLowerBounds.Circuit.lineDegrees, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl
