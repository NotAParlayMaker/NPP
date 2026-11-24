import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1754 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩], 10⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 6 ∧ C.output = 10 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 5 + p.2) ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4)) := by
  refine ⟨rfl, rfl, by decide +kernel, ?_⟩
  intro x
  have h : ∀ a b c d e : Bool, (fun i : Fin 5 => ![a, b, c, d, e] i) = ![a, b, c, d, e] → PEqualNP.CircuitLowerBounds.Circuit.eval (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩], 10⟩ : PEqualNP.CircuitLowerBounds.Circuit) [a, b, c, d, e] = ((a && b) || (a && c) || (a && d) || (a && e) || (b && d) || (b && e) || (c && d) || (c && e)) := by
    decide +kernel
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by
    simp [List.ofFn_succ]
  rw [hx]
  exact h (x 0) (x 1) (x 2) (x 3) (x 4) rfl
