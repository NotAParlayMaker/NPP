import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1159 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 4 && x 7)) x := by
  refine ⟨{ gates := [
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩], output := 14 }, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide +kernel
