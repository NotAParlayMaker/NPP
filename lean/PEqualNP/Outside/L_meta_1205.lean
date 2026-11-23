import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1205_aux

open PEqualNP.CircuitLowerBounds

def c1 : Circuit :=
  ⟨[⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [5, 8]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.and, [1, 0]⟩, ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k1 : ∀ a b c d e f g h : Bool,
    c1.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (b && c) || (d && e) || (d && f) || (e && g) || (f && h)) := by
  decide

end PEqualNP.Outside.L_meta_1205_aux

open PEqualNP.Outside.L_meta_1205_aux in
theorem PEqualNP.Outside.L_meta_1205 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 8 → Bool =>
          (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨c1, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c1]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
