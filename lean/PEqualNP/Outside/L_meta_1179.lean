import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1179_aux

open PEqualNP.CircuitLowerBounds

def c : Circuit := ⟨[
  ⟨GateOp.or, [1, 2]⟩,
  ⟨GateOp.or, [8, 3]⟩,
  ⟨GateOp.or, [9, 4]⟩,
  ⟨GateOp.and, [0, 10]⟩,
  ⟨GateOp.and, [2, 6]⟩,
  ⟨GateOp.or, [1, 7]⟩,
  ⟨GateOp.and, [5, 13]⟩,
  ⟨GateOp.or, [11, 12]⟩,
  ⟨GateOp.or, [15, 14]⟩
], 16⟩

theorem ev : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    c.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b2 && b6) || (b5 && b7)) := by
  decide

end PEqualNP.Outside.L_meta_1179_aux

open PEqualNP.Outside.L_meta_1179_aux in
theorem PEqualNP.Outside.L_meta_1179 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 5 && x 7)) x := by
  refine ⟨c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact ev (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
