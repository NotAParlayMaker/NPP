import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  refine ⟨Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true),
    Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false), ?_⟩
  refine ⟨rfl, Bool.true_eq_false.mp.mt id, ?_⟩
  simp only [PEqualNP.MetaComplexity.CoverPromise.vars,
    PEqualNP.MetaComplexity.CoverPromise.cvcFormula, List.mem_toFinset, List.mem_flatMap]
  exact ⟨[(PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)], by simp, by simp⟩
