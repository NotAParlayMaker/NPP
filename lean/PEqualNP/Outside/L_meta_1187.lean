import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1187 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨{ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], output := 17 }, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · intro x
    have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
    generalize x 0 = a; generalize x 1 = b; generalize x 2 = c; generalize x 3 = d; generalize x 4 = e; generalize x 5 = f; generalize x 6 = g; generalize x 7 = h
    revert a b c d e f g h
    decide
