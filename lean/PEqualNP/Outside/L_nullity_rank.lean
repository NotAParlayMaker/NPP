import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

/-- Rank–nullity (the nullity theorem): for `f : E →ₗ[ℂ] F` with `E` finite-dimensional over
`ℂ`, `finrank ℂ (range f) + finrank ℂ (ker f) = finrank ℂ E` (rank + nullity = dim E). -/
theorem L_nullity_rank {E F : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : E →ₗ[ℂ] F) :
    finrank ℂ (LinearMap.range f) + finrank ℂ (LinearMap.ker f) = finrank ℂ E :=
  LinearMap.finrank_range_add_finrank_ker f

end PEqualNP.Outside
