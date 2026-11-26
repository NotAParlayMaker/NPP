import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18231

end PEqualNP.Outside.L_meta_18231

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_18231 : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => decide (5 ≤ (List.ofFn x).count true)) 39 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [32, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 34]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [40, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [37, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 43]⟩], 44⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

