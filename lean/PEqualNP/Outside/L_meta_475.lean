import PEqualNP.Defs

open PEqualNP.MetaComplexity.CoverPromise

theorem PEqualNP.Outside.L_meta_475 : ∀ φ : PEqualNP.Search.CNF,
    ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex,
      (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  refine ⟨Sum.inl (fresh φ, false), Sum.inl (fresh φ, true), ?_⟩
  change fresh φ = fresh φ ∧ false ≠ true ∧ fresh φ ∈ vars (cvcFormula φ)
  refine ⟨rfl, by decide, ?_⟩
  simp only [vars, List.mem_toFinset, List.mem_flatMap, List.mem_map]
  refine ⟨[(fresh φ, false)], ?_, (fresh φ, false), by simp, rfl⟩
  simp [cvcFormula]
