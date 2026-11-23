import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_944 :
    (∀ C1 : PEqualNP.CircuitLowerBounds.Circuit, C1 = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 16]⟩], output := 20 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo C1 ∧ C1.size = 13 ∧ (∀ x1 : Fin 8 → Bool, (C1.eval (List.ofFn x1) = true ↔ ∃ u1 v1 : Fin 8, (u1.val, v1.val) ∈ ([(0, 1), (0, 2), (1, 2), (3, 4), (3, 7), (4, 7), (5, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x1 u1 = true ∧ x1 v1 = true))) := by
  intro C hC
  subst hC
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.ofFn_succ, List.ofFn_zero]
    revert x
    decide +revert
