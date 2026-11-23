import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1200

open PEqualNP.CircuitLowerBounds

def c : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k : ∀ a b c d e f g h : Bool,
    PEqualNP.Outside.L_meta_1200.c.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (a && d) || (b && e) || (c && f) || (e && g) || (g && h)) := by
  decide

end PEqualNP.Outside.L_meta_1200

theorem PEqualNP.Outside.L_meta_1200 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
        ∀ x : Fin 8 → Bool,
          C.eval (List.ofFn x) =
            (fun x : Fin 8 → Bool =>
              (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) ||
                (x 4 && x 6) || (x 6 && x 7))
              x := by
  refine ⟨PEqualNP.Outside.L_meta_1200.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1200.c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1200.k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
