import Mathlib
import PEqualNP.Defs

-- The circuit from the step, 9 gates of AND and OR, checked on all inputs.

namespace PEqualNP.Outside.L_meta_1177_witness

open PEqualNP.CircuitLowerBounds

-- The circuit.
def C : Circuit := ⟨[
  ⟨GateOp.or, [1, 2]⟩,
  ⟨GateOp.or, [8, 3]⟩,
  ⟨GateOp.or, [9, 4]⟩,
  ⟨GateOp.and, [0, 10]⟩,
  ⟨GateOp.or, [5, 6]⟩,
  ⟨GateOp.and, [1, 12]⟩,
  ⟨GateOp.and, [5, 7]⟩,
  ⟨GateOp.or, [11, 13]⟩,
  ⟨GateOp.or, [15, 14]⟩], 16⟩

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

end PEqualNP.Outside.L_meta_1177_witness

open PEqualNP.Outside.L_meta_1177_witness in
theorem PEqualNP.Outside.L_meta_1177 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 7)) x :=
  ⟨C, mono, by decide, by decide +kernel⟩
