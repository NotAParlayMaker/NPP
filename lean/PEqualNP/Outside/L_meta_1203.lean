import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_1203 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) ||
          (x 1 && x 4) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) x := by
  refine ⟨{ gates := [
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 4]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 }, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · intro x
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons, List.foldl_nil, List.ofFn_succ, List.ofFn_zero,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false,
      Bool.and_eq_true, Bool.or_eq_true]
    grind
