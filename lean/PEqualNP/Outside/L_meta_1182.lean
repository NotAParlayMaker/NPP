import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1182

def c : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩,
  ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [5, 12]⟩, ⟨GateOp.and, [6, 7]⟩,
  ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem k : ∀ a b d e f g h i : Bool, c.eval [a, b, d, e, f, g, h, i] =
    ((a && b) || (a && d) || (a && e) || (a && f) || (g && h) || (g && i) || (h && i)) := by
  decide

end PEqualNP.Outside.L_meta_1182

theorem PEqualNP.Outside.L_meta_1182 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 5 && x 6) || (x 5 && x 7) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1182.c, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1182.c]
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [h]
    exact PEqualNP.Outside.L_meta_1182.k (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
