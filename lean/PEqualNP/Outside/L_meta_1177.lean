import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1177

open PEqualNP.CircuitLowerBounds

def C : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem ev (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : C.eval [b0, b1, b2, b3, b4, b5, b6, b7] = ((b0 && b1) || (b0 && b2) || (b0 && b3) || (b0 && b4) || (b1 && b5) || (b1 && b6) || (b5 && b7)) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl

theorem ofFn_eq (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1177

theorem PEqualNP.Outside.L_meta_1177 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1177.C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1177.C]
  · intro x
    rw [PEqualNP.Outside.L_meta_1177.ofFn_eq x]
    exact PEqualNP.Outside.L_meta_1177.ev (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
