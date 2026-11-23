import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1193

def c : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k : ∀ v0 v1 v2 v3 v4 v5 v6 v7 : Bool, c.eval [v0, v1, v2, v3, v4, v5, v6, v7] =
    ((v0 && v1) || (v0 && v2) || (v0 && v3) || (v1 && v4) || (v1 && v5) || (v2 && v6) || (v4 && v7)) := by
  decide

end PEqualNP.Outside.L_meta_1193

theorem PEqualNP.Outside.L_meta_1193 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 4 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1193.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1193.c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1193.k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
