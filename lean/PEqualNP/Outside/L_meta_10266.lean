import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_10266 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 4) 23 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [20, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [22, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 23] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [24, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 25] }], output := 26 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    revert x
    decide +kernel
