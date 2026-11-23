import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1159_aux

open PEqualNP.CircuitLowerBounds

def c : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [11, 7]⟩,
    ⟨GateOp.and, [4, 12]⟩,
    ⟨GateOp.or, [10, 13]⟩], 14⟩

theorem k : ∀ a b c0 d e f g h : Bool,
    c.eval [a, b, c0, d, e, f, g, h] =
      ((a && b) || (a && c0) || (a && d) || (e && f) || (e && g) || (e && h)) := by
  decide

end PEqualNP.Outside.L_meta_1159_aux

theorem PEqualNP.Outside.L_meta_1159 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 4 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1159_aux.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1159_aux.c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1159_aux.k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
