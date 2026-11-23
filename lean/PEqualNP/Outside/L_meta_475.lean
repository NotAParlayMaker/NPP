import Mathlib.Data.List.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  refine ⟨Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true),
    Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false), ?_⟩
  simp [PEqualNP.MetaComplexity.CoverPromise.cvcGraph,
    PEqualNP.MetaComplexity.CoverPromise.satGraph,
    PEqualNP.MetaComplexity.CoverPromise.satAdj,
    PEqualNP.MetaComplexity.CoverPromise.vars,
    PEqualNP.MetaComplexity.CoverPromise.cvcFormula]
