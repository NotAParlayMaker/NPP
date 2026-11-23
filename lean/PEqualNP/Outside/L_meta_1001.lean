import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1001

open PEqualNP.CircuitLowerBounds

def viaCover : Circuit :=
  ⟨[
    ⟨.or, [1, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [12, 7]⟩,
    ⟨.and, [2, 13]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.and, [3, 15]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.and, [5, 17]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.and, [6, 19]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [21, 16]⟩,
    ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 20]⟩
  ], 24⟩

end PEqualNP.Outside.L_meta_1001

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_1001 : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 := by
  refine ⟨PEqualNP.Outside.L_meta_1001.viaCover, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_1001.viaCover, PEqualNP.MetaComplexity.FanInTwo]
  · decide
