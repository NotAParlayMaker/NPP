import PEqualNP.Defs

set_option maxHeartbeats 0

-- Finite check of an explicit 8-gate AND/OR circuit on 7 inputs: it is AO2 of size 8,
-- it computes the listed 3-by-4 bipartite edge function, and its re-read edges are
-- exactly the three listed pairs.
theorem PEqualNP.Outside.L_meta_3740 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }], output := 14 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 7 C ∧ C.size = 8 ∧
  (∀ x : Fin 7 → Bool, PEqualNP.MetaComplexity.circuitFun 7 C x = decide (∃ e ∈ ([(0, 6), (1, 5), (1, 6), (2, 3), (2, 4), (2, 6)] : List (Fin 7 × Fin 7)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 6), (1, 5), (1, 6), (2, 3), (2, 4), (2, 6)] : List (Fin 7 × Fin 7)), PEqualNP.Core.ReadTwiceAt 7 C (C.output - 7) e.1 e.2 ↔ e ∈ ([(0, 6), (1, 5), (1, 6)] : List (Fin 7 × Fin 7))) := by
  intro C hC
  subst C
  decide +kernel
