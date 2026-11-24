import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs

set_option maxRecDepth 40000 in
theorem PEqualNP.Outside.L_meta_1208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨⟨[
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide
