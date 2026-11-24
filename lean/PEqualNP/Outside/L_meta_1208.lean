import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_1208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨{
    gates := [
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 8] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 3] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 11] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 13] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 10] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 12] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 14] }],
    output := 17 }, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by simp⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · decide
