import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1204_aux

open PEqualNP.CircuitLowerBounds

def c : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [3, 11]⟩,
    ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.and, [6, 7]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [15, 12]⟩,
    ⟨GateOp.or, [16, 13]⟩,
    ⟨GateOp.or, [17, 14]⟩], 18⟩

theorem k : ∀ a b c0 d e f g h : Bool,
    c.eval [a, b, c0, d, e, f, g, h] =
      ((a && b) || (a && c0) || (b && c0) || (d && e) || (d && f) || (e && f) || (g && h)) := by
  decide

end PEqualNP.Outside.L_meta_1204_aux

theorem PEqualNP.Outside.L_meta_1204 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1204_aux.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1204_aux.c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1204_aux.k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
