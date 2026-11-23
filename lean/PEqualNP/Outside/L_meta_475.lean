import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  let y := PEqualNP.MetaComplexity.CoverPromise.fresh φ
  refine ⟨.inl (y, true), .inl (y, false), rfl, (by decide : true ≠ false), ?_⟩
  simp [y, PEqualNP.MetaComplexity.CoverPromise.vars, PEqualNP.MetaComplexity.CoverPromise.cvcFormula]
