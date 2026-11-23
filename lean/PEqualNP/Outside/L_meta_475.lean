import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  let y := PEqualNP.MetaComplexity.CoverPromise.fresh φ
  refine ⟨.inl (y, true), .inl (y, false), ?_⟩
  unfold PEqualNP.MetaComplexity.CoverPromise.cvcGraph
  unfold PEqualNP.MetaComplexity.CoverPromise.satGraph
  change PEqualNP.MetaComplexity.CoverPromise.satAdj (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ) (.inl (y, true)) (.inl (y, false))
  unfold PEqualNP.MetaComplexity.CoverPromise.satAdj
  refine ⟨rfl, by decide, ?_⟩
  unfold PEqualNP.MetaComplexity.CoverPromise.vars
  simp [PEqualNP.MetaComplexity.CoverPromise.cvcFormula, y, PEqualNP.MetaComplexity.CoverPromise.fresh]
