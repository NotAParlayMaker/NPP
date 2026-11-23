import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity.CoverPromise in
theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  refine ⟨Sum.inl (fresh φ, true), Sum.inl (fresh φ, false), ?_⟩
  simp [cvcGraph, satGraph, satAdj, vars, cvcFormula]
