import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1002
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  { gates := [⟨GateOp.or, [3, 1]⟩,
    ⟨GateOp.or, [8, 6]⟩,
    ⟨GateOp.and, [2, 9]⟩,
    ⟨GateOp.or, [5, 0]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.or, [5, 4]⟩,
    ⟨GateOp.or, [13, 3]⟩,
    ⟨GateOp.and, [7, 14]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.and, [4, 16]⟩,
    ⟨GateOp.or, [17, 10]⟩,
    ⟨GateOp.or, [18, 12]⟩,
    ⟨GateOp.or, [15, 19]⟩], output := 20 }

theorem witness_fanInTwo : PEqualNP.MetaComplexity.FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Set.mem_insert_iff, Set.mem_singleton_iff]

end PEqualNP.Outside.L_meta_1002

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.L_meta_1002 : ¬ (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13) := by
  intro h
  apply h
  refine ⟨PEqualNP.Outside.L_meta_1002.witness,
    PEqualNP.Outside.L_meta_1002.witness_fanInTwo, by decide, ?_⟩
  decide +kernel
