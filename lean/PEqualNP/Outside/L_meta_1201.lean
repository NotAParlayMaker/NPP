import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1201

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [15, 14]⟩], 16⟩

set_option maxHeartbeats 4000000 in
theorem keval : ∀ a b d e f g h i : Bool,
    circ.eval [a, b, d, e, f, g, h, i] =
      ((a && b) || (a && d) || (a && e) || (b && f) || (f && g) || (g && h) || (g && i)) := by
  decide

end PEqualNP.Outside.L_meta_1201

open PEqualNP.Outside.L_meta_1201

theorem PEqualNP.Outside.L_meta_1201 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧
      ∀ x : Fin 8 → Bool,
        C.eval (List.ofFn x) =
          (fun x : Fin 8 → Bool =>
            (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) ||
              (x 5 && x 6) || (x 5 && x 7))
            x := by
  refine ⟨circ, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, circ]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact keval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
