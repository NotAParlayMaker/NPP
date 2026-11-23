import Mathlib
import PEqualNP.Defs

-- The circuit from the step: wires 8 to 11 the OR of inputs 1 to 5, 12 its AND with input 0,
-- 13 and 14 the AND of 1, 2 and of 6, 7, then the OR of 12, 13, 14. Checked on all inputs.

namespace PEqualNP.Outside.L_meta_1168_witness

open PEqualNP.CircuitLowerBounds

-- The circuit.
def C : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩,
  ⟨GateOp.or, [10, 5]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.and, [6, 7]⟩,
  ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

-- Whether an operation is AND or OR.
def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem mono : PEqualNP.MetaComplexity.Monotone2 C := by
  have h : C.gates.all (fun g => okOp g.op && decide (g.inputs.length ≤ 2)) = true := by decide
  intro g hg
  have hg' := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg'
  obtain ⟨h1, h2⟩ := hg'
  refine ⟨?_, h2⟩
  revert h1
  cases g.op <;> simp [okOp]

end PEqualNP.Outside.L_meta_1168_witness

open PEqualNP.Outside.L_meta_1168_witness in
theorem PEqualNP.Outside.L_meta_1168 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 7)) x :=
  ⟨C, mono, by decide, by decide +kernel⟩
