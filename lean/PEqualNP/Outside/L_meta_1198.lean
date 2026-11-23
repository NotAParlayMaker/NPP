import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1198

open PEqualNP.CircuitLowerBounds

def C : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [12, 7]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem ev (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : C.eval [b0, b1, b2, b3, b4, b5, b6, b7] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b1 && b4) || (b2 && b5) || (b4 && b6) || (b4 && b7)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

theorem ofFn_eq (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1198

theorem PEqualNP.Outside.L_meta_1198 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 6) || (x 4 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1198.C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1198.C]
  · intro x
    rw [PEqualNP.Outside.L_meta_1198.ofFn_eq x]
    exact PEqualNP.Outside.L_meta_1198.ev (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
