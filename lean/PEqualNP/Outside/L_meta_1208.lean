import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1208_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Cstar : Circuit :=
  { gates := [
      { op := .or,  inputs := [1, 2] },
      { op := .and, inputs := [0, 8] },
      { op := .and, inputs := [1, 3] },
      { op := .or,  inputs := [2, 6] },
      { op := .and, inputs := [4, 11] },
      { op := .or,  inputs := [3, 7] },
      { op := .and, inputs := [5, 13] },
      { op := .or,  inputs := [9, 10] },
      { op := .or,  inputs := [12, 14] },
      { op := .or,  inputs := [15, 16] } ],
    output := 17 }

end PEqualNP.Outside.L_meta_1208_aux

open PEqualNP.Outside.L_meta_1208_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_1208 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
        ∀ x : Fin 8 → Bool,
          C.eval (List.ofFn x) =
            (fun x : Fin 8 → Bool =>
              (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) ||
              (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) ||
              (x 5 && x 7)) x := by
  refine ⟨Cstar, ?_, ?_, ?_⟩
  · simp [Monotone2, Cstar]
  · decide
  · decide
