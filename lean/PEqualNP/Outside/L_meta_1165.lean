import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1165

open PEqualNP.CircuitLowerBounds

def C0 : Circuit where
  gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [14, 12]⟩,
    ⟨GateOp.or, [15, 13]⟩]
  output := 16

theorem mono : PEqualNP.MetaComplexity.Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem size_le : C0.size ≤ 9 := by decide

set_option maxHeartbeats 4000000 in
theorem correct : ∀ x : Fin 8 → Bool, C0.eval (List.ofFn x) =
    ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1165

theorem PEqualNP.Outside.L_meta_1165 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1165.C0, PEqualNP.Outside.L_meta_1165.mono,
    PEqualNP.Outside.L_meta_1165.size_le, PEqualNP.Outside.L_meta_1165.correct⟩
