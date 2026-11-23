import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1184

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit :=
  { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩,
      ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [3, 5]⟩,
      ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [15, 13]⟩,
      ⟨GateOp.or, [16, 14]⟩],
    output := 17 }

theorem mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeC : C.size ≤ 10 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 10000000 in
theorem evalC : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
    (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x := by
  decide

end PEqualNP.Outside.L_meta_1184

open PEqualNP.Outside.L_meta_1184

theorem PEqualNP.Outside.L_meta_1184 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 6 && x 7)) x := by
  exact ⟨C, mono, sizeC, evalC⟩
