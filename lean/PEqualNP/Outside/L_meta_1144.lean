import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1144

open PEqualNP.CircuitLowerBounds

def C0 : Circuit where
  gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 12]⟩]
  output := 14

theorem mono : PEqualNP.MetaComplexity.Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem size_le : C0.size ≤ 7 := by decide

set_option maxHeartbeats 4000000 in
theorem correct : ∀ x : Fin 8 → Bool, C0.eval (List.ofFn x) =
    ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 6 && x 7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1144

theorem PEqualNP.Outside.L_meta_1144 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5) || (x 6 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1144.C0, PEqualNP.Outside.L_meta_1144.mono,
    PEqualNP.Outside.L_meta_1144.size_le, PEqualNP.Outside.L_meta_1144.correct⟩
