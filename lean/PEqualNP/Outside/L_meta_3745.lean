import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_3745 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 15] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 8 C ∧ C.size = 9 ∧
  (∀ x : Fin 8 → Bool, PEqualNP.MetaComplexity.circuitFun 8 C x = decide (∃ e ∈ ([(0, 7), (1, 7), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7)] : List (Fin 8 × Fin 8)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 7), (1, 7), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (3, 7)] : List (Fin 8 × Fin 8)), PEqualNP.Core.ReadTwiceAt 8 C (C.output - 8) e.1 e.2 ↔ e ∈ ([(2, 5), (2, 6), (3, 4), (3, 5), (3, 6)] : List (Fin 8 × Fin 8))) := by
  intro C hC
  subst hC
  let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  and_intros <;> first
    | rfl
    | decide +kernel
    | decide
    | (intro g hg; fin_cases hg <;> simp)
    | simp +decide
