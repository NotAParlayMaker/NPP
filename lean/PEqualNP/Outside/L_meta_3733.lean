import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3733 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, C = ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit) →
  PEqualNP.TopForm.IsAO2 7 C ∧ C.size = 7 ∧
  (∀ x : Fin 7 → Bool, PEqualNP.MetaComplexity.circuitFun 7 C x = decide (∃ e ∈ ([(0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), x e.1 = true ∧ x e.2 = true)) ∧
  (∀ e ∈ ([(0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6)] : List (Fin 7 × Fin 7)), PEqualNP.Core.ReadTwiceAt 7 C (C.output - 7) e.1 e.2 ↔ e ∈ ([(0, 5), (0, 6)] : List (Fin 7 × Fin 7))) := by
  rintro C rfl
  refine ⟨by decide, rfl, ?_, by decide⟩
  intro x
  have hof : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6] := by
    simp [List.ofFn_succ]
  rw [PEqualNP.MetaComplexity.circuitFun, hof]
  have hbool : ∀ b0 b1 b2 b3 b4 b5 b6 : Bool,
      ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 12] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit).eval [b0, b1, b2, b3, b4, b5, b6] =
      ((b0 && b5) || (b0 && b6) || (b1 && b3) || (b1 && b4) || (b1 && b5) || (b1 && b6) || (b2 && b3) || (b2 && b4) || (b2 && b5) || (b2 && b6)) := by
    decide
  rw [hbool]
  apply Bool.eq_iff_iff.mpr
  simp [Bool.or_eq_true, Bool.and_eq_true, or_assoc]
