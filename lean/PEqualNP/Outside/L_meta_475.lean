import PEqualNP.Defs

open PEqualNP.Search PEqualNP.MetaComplexity.CoverPromise

theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  refine ⟨Sum.inr (φ.length, 0), Sum.inl (fresh φ, false), ?_⟩
  show satAdj (cvcFormula φ) (Sum.inr (φ.length, 0)) (Sum.inl (fresh φ, false))
  simp [satAdj, clauseAt, cvcFormula, List.getD_eq_getElem?_getD]
