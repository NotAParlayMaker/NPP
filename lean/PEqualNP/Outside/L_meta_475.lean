import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_475 :
    ∀ φ : PEqualNP.Search.CNF,
      ∃ u v : PEqualNP.MetaComplexity.CoverPromise.Vertex,
        (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ).Adj u v := by
  intro φ
  have hlen : (φ.map (fun C => C ++ [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, true)])).length
      = φ.length := by simp
  have hget : (PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ)[φ.length]?
      = some [(PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)] := by
    unfold PEqualNP.MetaComplexity.CoverPromise.cvcFormula
    rw [List.getElem?_append_right (by rw [hlen])]
    rw [hlen]
    simp
  refine ⟨Sum.inr (φ.length, 0),
    Sum.inl (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false), ?_⟩
  show ((PEqualNP.MetaComplexity.CoverPromise.cvcFormula φ).getD φ.length [])[0]?
      = some (PEqualNP.MetaComplexity.CoverPromise.fresh φ, false)
  rw [List.getD_eq_getElem?_getD, hget]
  rfl
