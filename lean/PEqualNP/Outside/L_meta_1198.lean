import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1198

open PEqualNP.CircuitLowerBounds

def c : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [12, 7]⟩,
    ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem keval : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : Bool,
    c.eval [x0, x1, x2, x3, x4, x5, x6, x7] =
      ((x0 && x1) || (x0 && x2) || (x0 && x3) || (x1 && x4) || (x2 && x5) ||
        (x4 && x6) || (x4 && x7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1198

theorem PEqualNP.Outside.L_meta_1198 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 4 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1198.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1198.c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1198.keval (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
