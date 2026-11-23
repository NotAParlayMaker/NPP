import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1003

/-- Cover orientation circuit of size 13 for the Petersen-minus-adjacent graph on 8 vertices. -/
def C : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 4]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 16]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 14]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 17]⟩],
    output := 20 }

theorem C_fanInTwo : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem C_correct :
    ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) =
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
          (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) := by
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
  rw [hx]
  simp only [C, PEqualNP.CircuitLowerBounds.Circuit.eval,
    PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, id_eq, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Bool.or_false, Bool.and_true]
  revert x
  decide

end PEqualNP.Outside.L_meta_1003

theorem PEqualNP.Outside.L_meta_1003 :
    PEqualNP.MetaComplexity.HasCircuitSize 8
      (fun x : Fin 8 → Bool =>
        (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) ||
          (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4))
      13 := by
  refine ⟨PEqualNP.Outside.L_meta_1003.C, PEqualNP.Outside.L_meta_1003.C_fanInTwo, ?_,
    PEqualNP.Outside.L_meta_1003.C_correct⟩
  decide
