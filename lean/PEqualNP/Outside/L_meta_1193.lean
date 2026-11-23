import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1193_aux

open PEqualNP.CircuitLowerBounds

def c1 : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k1 : ∀ a b c d e f g h : Bool,
    c1.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (b && e) || (b && f) || (c && g) || (e && h)) := by
  decide

end PEqualNP.Outside.L_meta_1193_aux

open PEqualNP.Outside.L_meta_1193_aux in
theorem PEqualNP.Outside.L_meta_1193 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 8 → Bool =>
          (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) ||
            (x 2 && x 6) || (x 4 && x 7)) x := by
  refine ⟨c1, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c1]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
