import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity.CoverPromise

theorem PEqualNP.Outside.L_meta_475 :
    ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  refine ⟨.inl (fresh φ, true), .inl (fresh φ, false), ?_⟩
  change fresh φ = fresh φ ∧ true ≠ false ∧ fresh φ ∈ vars (cvcFormula φ)
  simp [vars, cvcFormula]
