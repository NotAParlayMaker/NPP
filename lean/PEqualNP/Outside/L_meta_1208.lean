import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1208

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[
  ⟨GateOp.or, [1, 2]⟩,
  ⟨GateOp.and, [0, 8]⟩,
  ⟨GateOp.and, [1, 3]⟩,
  ⟨GateOp.or, [2, 6]⟩,
  ⟨GateOp.and, [4, 11]⟩,
  ⟨GateOp.or, [3, 7]⟩,
  ⟨GateOp.and, [5, 13]⟩,
  ⟨GateOp.or, [9, 10]⟩,
  ⟨GateOp.or, [15, 12]⟩,
  ⟨GateOp.or, [16, 14]⟩
], 17⟩

theorem ok0 : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]
    · decide

theorem ev0 : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    C0.eval [b0, b1, b2, b3, b4, b5, b6, b7] =
      ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b6) || (b5 && b7)) := by
  decide +kernel

theorem ofFn8 (x : Fin 8 → Bool) : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1208

theorem PEqualNP.Outside.L_meta_1208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x :=
  ⟨PEqualNP.Outside.L_meta_1208.C0, PEqualNP.Outside.L_meta_1208.ok0, by decide, fun x => by
    rw [PEqualNP.Outside.L_meta_1208.ofFn8]
    exact PEqualNP.Outside.L_meta_1208.ev0 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)⟩
