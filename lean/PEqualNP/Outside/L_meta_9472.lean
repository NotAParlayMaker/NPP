import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9472
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- An 11-gate circuit of AND and OR gates (no NOT) for: at least 3 of 5 inputs are true.
-- Wires 0..4 are the inputs; gate number j is wire 5 + j; the output is the last gate.
def circ : Circuit := ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩

theorem circ_fan : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circ_eval : ∀ b0 b1 b2 b3 b4 : Bool,
    circ.eval [b0, b1, b2, b3, b4] = decide (3 ≤ ([b0, b1, b2, b3, b4] : List Bool).count true) := by decide

end PEqualNP.Outside.L_meta_9472

open PEqualNP.Outside.L_meta_9472 in
theorem PEqualNP.Outside.L_meta_9472 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => decide (3 ≤ ((List.ofFn x).count true))) 11 := by
  refine ⟨circ, circ_fan, by decide, fun x => ?_⟩
  have hl : List.ofFn x = [x 0, x 1, x 2, x 3, x 4] := by simp [List.ofFn_succ]
  rw [hl]
  exact circ_eval (x 0) (x 1) (x 2) (x 3) (x 4)
