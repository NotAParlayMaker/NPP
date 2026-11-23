import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1183_aux

open PEqualNP.CircuitLowerBounds

def c1 : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [8, 2]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k1 : ∀ a b c d e f g h : Bool,
    c1.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (b && c) || (b && e) || (c && f) || (g && h)) := by
  decide

end PEqualNP.Outside.L_meta_1183_aux

open PEqualNP.Outside.L_meta_1183_aux in
theorem PEqualNP.Outside.L_meta_1183 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 8 → Bool =>
          (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 6 && x 7)) x := by
  refine ⟨c1, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c1]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
