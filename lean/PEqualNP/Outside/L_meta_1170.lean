import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1170 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  refine ⟨⟨[
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 14]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires,
      PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ,
      List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false, Bool.and_true]
    cases x 0 <;> simp
