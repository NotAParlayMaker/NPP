import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_3744 :
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 7 C ∧ C.size = 9 ∧
  (∀ x : Fin 7 → Bool, PEqualNP.MetaComplexity.circuitFun 7 C x = decide (∃ e ∈ ([(0, 5), (0, 6), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 5), (0, 6), (1, 4), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), PEqualNP.Core.ReadTwiceAt 7 C (C.output - 7) e.1 e.2 ↔ e ∈ ([(0, 5), (0, 6), (2, 3), (2, 5)] : List (Fin 7 × Fin 7))) := by
  rintro C rfl
  decide +kernel
