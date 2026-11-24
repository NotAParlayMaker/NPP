import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1754

lemma eval_bool (b0 b1 b2 b3 b4 : Bool) :
    (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩,
       ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
       ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩,
       ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
       ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩,
       ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩], 10⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval
      [b0, b1, b2, b3, b4] =
    ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) ||
     (b1 && b3) || (b1 && b4) || (b2 && b3) || (b2 && b4)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> rfl

end PEqualNP.Outside.L_meta_1754

theorem PEqualNP.Outside.L_meta_1754 : let C : PEqualNP.CircuitLowerBounds.Circuit := (⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩], 10⟩ : PEqualNP.CircuitLowerBounds.Circuit); C.gates.length = 6 ∧ C.output = 10 ∧ (∀ p ∈ C.gates.zipIdx, ((p.1.op.eval [] = true ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a && b)) ∨ (p.1.op.eval [] = false ∧ ∀ a b : Bool, p.1.op.eval [a, b] = (a || b))) ∧ p.1.inputs.length = 2 ∧ ∀ i ∈ p.1.inputs, i < 5 + p.2) ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4)) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · decide
  · intro x
    exact PEqualNP.Outside.L_meta_1754.eval_bool (x 0) (x 1) (x 2) (x 3) (x 4)
