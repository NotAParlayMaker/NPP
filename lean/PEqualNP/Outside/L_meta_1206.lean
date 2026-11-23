import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1206

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

set_option maxHeartbeats 4000000 in
theorem keval : ∀ a b d e f g h i : Bool,
    circ.eval [a, b, d, e, f, g, h, i] =
      ((a && b) || (a && d) || (b && e) || (d && f) || (e && f) || (g && h) || (g && i)) := by
  decide

end PEqualNP.Outside.L_meta_1206

open PEqualNP.Outside.L_meta_1206

theorem PEqualNP.Outside.L_meta_1206 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 8 → Bool,
        C.eval (List.ofFn x) =
          (fun x : Fin 8 → Bool =>
            (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 4) ||
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
