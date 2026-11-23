import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 :
    ∀ φ : PEqualNP.Search.CNF, ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex, (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  refine ⟨Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, true),
    Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false), ?_⟩
  show PEqualNP.MetaComplexity.CoverPromise.fresh φ = PEqualNP.MetaComplexity.CoverPromise.fresh φ ∧
    true ≠ false ∧ PEqualNP.MetaComplexity.CoverPromise.fresh φ ∈
      PEqualNP.MetaComplexity.CoverPromise.vars (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ)
  refine ⟨rfl, by decide, ?_⟩
  rw [PEqualNP.MetaComplexity.CoverPromise.vars, PEqualNP.MetaComplexity.CoverPromise.cvcFormula,
    List.mem_toFinset, List.mem_flatMap]
  exact ⟨[(PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)],
    List.mem_append_right _ (List.mem_singleton.2 rfl),
    List.mem_map.2 ⟨(PEqualNP.MetaComplexity.CoverPromise.fresh φ, false), List.mem_singleton.2 rfl, rfl⟩⟩
