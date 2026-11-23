import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1003

open PEqualNP.CircuitLowerBounds

def C : Circuit where
  gates :=
    [⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [1, 9]⟩,
     ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [2, 11]⟩,
     ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.and, [4, 14]⟩,
     ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [7, 16]⟩,
     ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.or, [18, 19]⟩]
  output := 20

lemma fanIn : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp

lemma size : C.size ≤ 13 := by
  simp [Circuit.size, C]

lemma evalAll : ∀ a b c d e f g h : Bool,
    C.eval [a, b, c, d, e, f, g, h] =
      ((a && b) || (b && c) || (c && d) || (a && e) || (b && f) || (c && g) || (d && h) ||
        (e && g) || (f && h) || (h && e)) := by
  decide

end PEqualNP.Outside.L_meta_1003

theorem PEqualNP.Outside.L_meta_1003 : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13 := by
  refine ⟨PEqualNP.Outside.L_meta_1003.C, PEqualNP.Outside.L_meta_1003.fanIn,
    PEqualNP.Outside.L_meta_1003.size, ?_⟩
  intro x
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
    simp [List.ofFn_succ]
  rw [hx]
  exact PEqualNP.Outside.L_meta_1003.evalAll _ _ _ _ _ _ _ _
