import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1003

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [15, 4]⟩, ⟨GateOp.and, [7, 16]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [18, 14]⟩, ⟨GateOp.or, [19, 17]⟩], 20⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem ev0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    C0.eval [b0, b1, b2, b3, b4, b5, b6, b7] = ((b0 && b1) || (b1 && b2) || (b2 && b3) || (b0 && b4) || (b1 && b5) || (b2 && b6) || (b3 && b7) || (b4 && b6) || (b5 && b7) || (b7 && b4)) := by
  decide +kernel

theorem ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1003

theorem PEqualNP.Outside.L_meta_1003 : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13 :=
  ⟨PEqualNP.Outside.L_meta_1003.C0, PEqualNP.Outside.L_meta_1003.ok0, by decide, fun x => by
      rw [PEqualNP.Outside.L_meta_1003.ofFn8]
      exact PEqualNP.Outside.L_meta_1003.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
