import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1001_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sixteen : Circuit :=
  ⟨[⟨.or, [1, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [12, 8]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.and, [7, 14]⟩,
    ⟨.and, [8, 15]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [22, 23]⟩], 24⟩

theorem sixteen_ok : HasCircuitSize 9
  (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 := by
  refine ⟨sixteen, ?_, by decide, ?_⟩
  · intro g hg
    simp only [sixteen, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ⟨by first | exact Or.inl rfl | exact Or.inr (Or.inl rfl), by decide⟩
  · intro x
    dsimp only
    rw [show List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] from rfl]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> cases x 6 <;> cases x 7 <;> cases x 8 <;> decide

end PEqualNP.Outside.L_meta_1001_aux

theorem PEqualNP.Outside.L_meta_1001 : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 :=
  PEqualNP.Outside.L_meta_1001_aux.sixteen_ok
