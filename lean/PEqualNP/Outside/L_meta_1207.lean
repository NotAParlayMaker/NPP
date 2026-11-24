import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1207

instance : DecidableEq PEqualNP.CircuitLowerBounds.GateOp :=
  PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

instance : DecidableEq Gate := PEqualNP.CircuitMoves.gateDecEq

def ckt : Circuit :=
  { gates := [ ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 5]⟩,
               ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 12]⟩,
               ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [14, 13]⟩, ⟨GateOp.and, [6, 7]⟩,
               ⟨GateOp.or, [15, 16]⟩ ],
    output := 17 }

end PEqualNP.Outside.L_meta_1207

open PEqualNP.Outside.L_meta_1207 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_1207 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨ckt, ?_, ?_, ?_⟩
  · simp only [PEqualNP.MetaComplexity.Monotone2]
    intro g hg
    simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide⟩
  · decide
  · decide
