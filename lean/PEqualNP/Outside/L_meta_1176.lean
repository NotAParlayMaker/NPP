import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_1176

def C : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [1, 12]⟩,
    ⟨GateOp.and, [2, 7]⟩,
    ⟨GateOp.or, [11, 13]⟩,
    ⟨GateOp.or, [15, 14]⟩], 16⟩

theorem fanin : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem size_le : C.size ≤ 9 := by
  simp [C, Circuit.size]

theorem eval_eq : ∀ x : Fin 8 → Bool,
    C.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1176

theorem PEqualNP.Outside.L_meta_1176 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1176.C, PEqualNP.Outside.L_meta_1176.fanin, PEqualNP.Outside.L_meta_1176.size_le, PEqualNP.Outside.L_meta_1176.eval_eq⟩
