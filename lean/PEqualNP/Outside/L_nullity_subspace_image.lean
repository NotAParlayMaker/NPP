import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

/-- Rank–nullity of the map `f ∘ K.subtype : K →ₗ[ℂ] W` (the rank of the image of `f` on `K` plus
the nullity on `K` equals `finrank ℂ K`). -/
theorem L_nullity_subspace_image {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] (K : Submodule ℂ V) (f : V →ₗ[ℂ] W) :
    finrank ℂ (LinearMap.range (f.comp K.subtype)) +
      finrank ℂ (LinearMap.ker (f.comp K.subtype)) = finrank ℂ K :=
  LinearMap.finrank_range_add_finrank_ker (f.comp K.subtype)

end PEqualNP.Outside
