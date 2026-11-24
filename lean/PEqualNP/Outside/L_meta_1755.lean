import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1755 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [27, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 28]⟩], 29⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 20 ∧ C.output = 29 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 10 + p.2) ∧ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
  intro C
  refine ⟨rfl, rfl, by decide +kernel, ?_⟩
  intro x
  have inputList : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
    simp [List.ofFn_succ]
  rw [inputList]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  generalize x 4 = b4
  generalize x 5 = b5
  generalize x 6 = b6
  generalize x 7 = b7
  generalize x 8 = b8
  generalize x 9 = b9
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
  decide +kernel
