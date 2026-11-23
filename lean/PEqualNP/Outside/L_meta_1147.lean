import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1147

open PEqualNP.CircuitLowerBounds

def c : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [3, 10]⟩,
    ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [13, 12]⟩], 14⟩

theorem k : ∀ a b c d e f g h : Bool,
    PEqualNP.Outside.L_meta_1147.c.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (a && c) || (d && e) || (d && f) || (g && h)) := by
  decide

end PEqualNP.Outside.L_meta_1147

theorem PEqualNP.Outside.L_meta_1147 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧
        ∀ x : Fin 8 → Bool,
          C.eval (List.ofFn x) =
            (fun x : Fin 8 → Bool =>
              (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 6 && x 7))
              x := by
  refine ⟨PEqualNP.Outside.L_meta_1147.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1147.c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1147.k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
