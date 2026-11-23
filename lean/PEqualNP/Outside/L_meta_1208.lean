import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_1208

def C : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [4, 11]⟩,
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.and, [5, 13]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [15, 12]⟩,
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
        (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1208

theorem PEqualNP.Outside.L_meta_1208 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 10 ∧
      ∀ x : Fin 8 → Bool,
        C.eval (List.ofFn x) =
          ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) ||
            (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) :=
  ⟨PEqualNP.Outside.L_meta_1208.C,
    PEqualNP.Outside.L_meta_1208.fanin,
    PEqualNP.Outside.L_meta_1208.size_le,
    PEqualNP.Outside.L_meta_1208.eval_eq⟩
