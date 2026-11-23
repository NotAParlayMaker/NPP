import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

/-- Rank–nullity on a subspace: for `p : V →ₗ[ℂ] W` and a submodule `K` of `V` with `V`
finite-dimensional, `finrank ℂ (K.map p) + finrank ℂ (K ⊓ ker p) = finrank ℂ K`
(rank + nullity of the restriction to `K` equals the dimension of `K`). -/
theorem L_nullity_subspace {V W : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] (K : Submodule ℂ V) (p : V →ₗ[ℂ] W) :
    finrank ℂ (K.map p) + finrank ℂ ↥(K ⊓ LinearMap.ker p) = finrank ℂ K := by
  have h := LinearMap.finrank_range_add_finrank_ker (p.domRestrict K)
  rw [LinearMap.range_domRestrict] at h
  have h2 : (LinearMap.ker (p.domRestrict K)).map K.subtype = K ⊓ LinearMap.ker p := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have h3 : finrank ℂ ((LinearMap.ker (p.domRestrict K)).map K.subtype) =
      finrank ℂ (LinearMap.ker (p.domRestrict K)) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ K.injective_subtype _)).symm
  rw [h2] at h3
  omega

end PEqualNP.Outside
