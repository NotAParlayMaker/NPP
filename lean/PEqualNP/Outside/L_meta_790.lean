import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_790 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    C = ({ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit) →
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 7 ∧ (∀ x : Fin 6 → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6,
        (u.val, v.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
