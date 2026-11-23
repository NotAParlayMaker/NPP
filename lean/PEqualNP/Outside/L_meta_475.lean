import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  refine ⟨Sum.inr (φ.length, 0),
    Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false), ?_⟩
  show (PEqualNP.MetaComplexity.CoverPromise.clauseAt
    (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) φ.length)[0]? = some _
  simp [PEqualNP.MetaComplexity.CoverPromise.clauseAt,
    PEqualNP.MetaComplexity.CoverPromise.cvcFormula]
