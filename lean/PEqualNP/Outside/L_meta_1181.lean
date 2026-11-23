import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1181

open PEqualNP.CircuitLowerBounds

def edgeCircuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [1, 5]⟩,
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.and, [6, 13]⟩,
    ⟨GateOp.or, [11, 12]⟩,
    ⟨GateOp.or, [15, 14]⟩]
  output := 16

theorem edgeCircuit_monotone : PEqualNP.MetaComplexity.Monotone2 edgeCircuit := by
  intro gate hgate
  simp only [edgeCircuit, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem edgeCircuit_eval (a b c d e f g h : Bool) :
    edgeCircuit.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (a && e) || (b && f) || (f && g) || (g && h)) := by
  revert a b c d e f g h
  decide

theorem inputList (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1181

theorem PEqualNP.Outside.L_meta_1181 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool,
        C.eval (List.ofFn x) = (fun x : Fin 8 → Bool =>
          (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) ||
          (x 1 && x 5) || (x 5 && x 6) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1181.edgeCircuit,
    PEqualNP.Outside.L_meta_1181.edgeCircuit_monotone, by decide, ?_⟩
  intro x
  rw [PEqualNP.Outside.L_meta_1181.inputList x]
  exact PEqualNP.Outside.L_meta_1181.edgeCircuit_eval
    (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
