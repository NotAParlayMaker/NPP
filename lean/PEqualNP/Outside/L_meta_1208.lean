import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1208
def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [6, 2]⟩
      , ⟨GateOp.and, [4, 8]⟩
      , ⟨GateOp.and, [2, 0]⟩
      , ⟨GateOp.or, [0, 3]⟩
      , ⟨GateOp.and, [1, 11]⟩
      , ⟨GateOp.or, [3, 7]⟩
      , ⟨GateOp.and, [5, 13]⟩
      , ⟨GateOp.or, [9, 10]⟩
      , ⟨GateOp.or, [12, 14]⟩
      , ⟨GateOp.or, [15, 16]⟩
      ]
    output := 17 }
end PEqualNP.Outside.L_meta_1208

open PEqualNP.Outside.L_meta_1208

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨C, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · decide
  · decide
