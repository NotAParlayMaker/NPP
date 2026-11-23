import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_179

open PEqualNP.MetaComplexity

private def W : DMFormula 6 :=
  DMFormula.and
    (DMFormula.or (DMFormula.lit 0 true) (DMFormula.lit 1 true))
    (DMFormula.or (DMFormula.lit 2 true)
      (DMFormula.or (DMFormula.lit 3 true)
        (DMFormula.and
          (DMFormula.or (DMFormula.lit 0 true) (DMFormula.lit 5 true))
          (DMFormula.or (DMFormula.lit 1 true) (DMFormula.lit 4 true)))))

end PEqualNP.Outside.L_meta_179

theorem PEqualNP.Outside.L_meta_179 :
    PEqualNP.MetaComplexity.HasLeafSize 6
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3) ||
          (x 0 && x 4) || (x 1 && x 5)) 8 := by
  refine ⟨PEqualNP.Outside.L_meta_179.W, ?_, ?_⟩
  · decide
  · decide
