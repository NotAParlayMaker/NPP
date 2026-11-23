import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_179 : PEqualNP.MetaComplexity.HasLeafSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 5)) 8 := by
  refine ⟨PEqualNP.MetaComplexity.DMFormula.and
    (PEqualNP.MetaComplexity.DMFormula.or
      (PEqualNP.MetaComplexity.DMFormula.lit 0 true)
      (PEqualNP.MetaComplexity.DMFormula.lit 1 true))
    (PEqualNP.MetaComplexity.DMFormula.or
      (PEqualNP.MetaComplexity.DMFormula.lit 2 true)
      (PEqualNP.MetaComplexity.DMFormula.or
        (PEqualNP.MetaComplexity.DMFormula.lit 3 true)
        (PEqualNP.MetaComplexity.DMFormula.and
          (PEqualNP.MetaComplexity.DMFormula.or
            (PEqualNP.MetaComplexity.DMFormula.lit 0 true)
            (PEqualNP.MetaComplexity.DMFormula.lit 5 true))
          (PEqualNP.MetaComplexity.DMFormula.or
            (PEqualNP.MetaComplexity.DMFormula.lit 1 true)
            (PEqualNP.MetaComplexity.DMFormula.lit 4 true))))), by decide, ?_⟩
  intro x
  simp only [PEqualNP.MetaComplexity.DMFormula.eval, ite_true]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> rfl
