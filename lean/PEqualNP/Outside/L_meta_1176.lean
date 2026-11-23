import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1176

def c : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : Bool, c.eval [v0, v1, v2, v3, v4, v5, v6, v7] =
    ((v0 && v1) || (v0 && v2) || (v0 && v3) || (v0 && v4) || (v1 && v5) || (v1 && v6) || (v2 && v7)) := by
  decide

end PEqualNP.Outside.L_meta_1176

theorem PEqualNP.Outside.L_meta_1176 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1176.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1176.c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1176.k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
