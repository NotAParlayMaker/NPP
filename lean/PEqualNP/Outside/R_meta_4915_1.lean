import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4915_1
  (h1 : True → (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : ℕ), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x4 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x4))
  (h2 : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : ℕ), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x4 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x4) → (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : ℕ), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x4 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x4))
  : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : ℕ), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.SharedBlockCost.HasSharedBlockCost x2 x4 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x4 := by
  exact h2 (h1 trivial)
