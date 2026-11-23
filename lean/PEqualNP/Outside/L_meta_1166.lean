import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1166

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.or, [10, 5]⟩, ⟨GateOp.or, [11, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [0, 13]⟩], 14⟩

theorem k1 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : Bool, c1.eval [x0, x1, x2, x3, x4, x5, x6, x7] = ((x0 && x1) || (x0 && x2) || (x0 && x3) || (x0 && x4) || (x0 && x5) || (x0 && x6) || (x0 && x7)) := by
  decide

end PEqualNP.Outside.L_meta_1166

theorem PEqualNP.Outside.L_meta_1166 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1166.c1, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1166.c1]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1166.k1 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
