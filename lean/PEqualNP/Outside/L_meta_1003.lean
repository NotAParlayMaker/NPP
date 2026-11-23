import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1003

open PEqualNP.CircuitLowerBounds

-- one star for each vertex of the cover 1, 2, 4, 7, then three OR gates
def circ : Circuit :=
  { gates := [⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [1, 9]⟩,
      ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [2, 11]⟩,
      ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.and, [4, 14]⟩,
      ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [7, 16]⟩,
      ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [18, 15]⟩, ⟨GateOp.or, [19, 17]⟩], output := 20 }

theorem eval_bits (a b c d e f g h : Bool) :
    circ.eval [a, b, c, d, e, f, g, h] = ((a && b) || (b && c) || (c && d) || (a && e) ||
      (b && f) || (c && g) || (d && h) || (e && g) || (f && h) || (h && e)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;> rfl

theorem ofFn8 (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

theorem fan : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp [circ] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_1003

theorem PEqualNP.Outside.L_meta_1003 : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13 := by
  refine ⟨PEqualNP.Outside.L_meta_1003.circ, PEqualNP.Outside.L_meta_1003.fan, by decide, ?_⟩
  intro x
  rw [PEqualNP.Outside.L_meta_1003.ofFn8, PEqualNP.Outside.L_meta_1003.eval_bits]
