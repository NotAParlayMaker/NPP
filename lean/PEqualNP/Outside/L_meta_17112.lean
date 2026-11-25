import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17112 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size = (11 : ℕ) ∧ x1.output = (24 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2 ∧ x5 ≠ (0 : ℕ) ∧ x5 ≠ (7 : ℕ) ∧ x6 ≠ (0 : ℕ) ∧ x6 ≠ (7 : ℕ)) ∧ ∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true ↔ ∃ (x3 : Fin (7 : ℕ)) (x4 : Fin (7 : ℕ)), ((1 : ℕ) ≤ ↑x4 ∧ ↑x4 ≤ (3 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x4) = Bool.true := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 22] }], output := 24 } : PEqualNP.CircuitLowerBounds.Circuit), rfl, rfl, ?_, ?_⟩
  · intro i g hg
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp at hg <;> subst hg <;> simp
  · intro x
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ]
    simp only [Fin.exists_fin_succ, Fin.exists_fin_zero]
    simp [Fin.ext_iff]
    cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> cases x 8 <;> cases x 9 <;> cases x 10 <;> simp
