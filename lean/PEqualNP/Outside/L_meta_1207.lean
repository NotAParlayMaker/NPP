import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_1207

def C : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [3, 10]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.and, [4, 12]⟩,
    ⟨GateOp.and, [6, 7]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [15, 13]⟩,
    ⟨GateOp.or, [16, 14]⟩], 17⟩

theorem fanin : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem size_le : C.size ≤ 10 := by
  simp [C, Circuit.size]

theorem eval_eq : ∀ x : Fin 8 → Bool,
    C.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) ||
        (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1207

theorem PEqualNP.Outside.L_meta_1207 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 8 → Bool,
        C.eval (List.ofFn x) =
          ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) ||
            (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) :=
  ⟨PEqualNP.Outside.L_meta_1207.C,
    PEqualNP.Outside.L_meta_1207.fanin,
    PEqualNP.Outside.L_meta_1207.size_le,
    PEqualNP.Outside.L_meta_1207.eval_eq⟩
