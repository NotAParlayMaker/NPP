import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1205_aux

open PEqualNP.CircuitLowerBounds

def c : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.and, [5, 13]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [15, 12]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem k : ∀ a b d e f g h i : Bool, c.eval [a, b, d, e, f, g, h, i] = ((a && b) || (a && d) || (b && d) || (e && f) || (e && g) || (f && h) || (g && i)) := by
  decide

end PEqualNP.Outside.L_meta_1205_aux

open PEqualNP.Outside.L_meta_1205_aux in
theorem PEqualNP.Outside.L_meta_1205 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
