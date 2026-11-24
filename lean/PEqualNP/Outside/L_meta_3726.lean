import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3726 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 10] }], output := 11 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 6 C ∧ C.size = 6 ∧
  (∀ x : Fin 6 → Bool, PEqualNP.MetaComplexity.circuitFun 6 C x = decide (∃ e ∈ ([(0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5)] : List (Fin 6 × Fin 6)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5)] : List (Fin 6 × Fin 6)), PEqualNP.Core.ReadTwiceAt 6 C (C.output - 6) e.1 e.2 ↔ e ∈ ([(1, 2), (1, 3)] : List (Fin 6 × Fin 6))) := by
  rintro C rfl
  refine ⟨by decide, rfl, ?_, ?_⟩
  · decide
  · decide
