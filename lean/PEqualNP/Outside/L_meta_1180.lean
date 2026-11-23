import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1180 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6) || (x 5 && x 7)) x := by
  refine ⟨{ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 4]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 14]⟩], output := 15 }, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · intro x
    have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      funext i
      fin_cases i <;> rfl
    rw [hx]
    generalize x 0 = a; generalize x 1 = b; generalize x 2 = c; generalize x 3 = d
    generalize x 4 = e; generalize x 5 = f; generalize x 6 = g; generalize x 7 = h
    revert a b c d e f g h
    decide
