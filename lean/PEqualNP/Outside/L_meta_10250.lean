import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_10250

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.not, [5]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.not, [11]⟩,
    ⟨.not, [2]⟩,
    ⟨.and, [9, 15]⟩,
    ⟨.and, [5, 2]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.and, [9, 2]⟩,
    ⟨.and, [8, 15]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.and, [8, 2]⟩,
    ⟨.and, [5, 15]⟩,
    ⟨.or, [22, 23]⟩,
    ⟨.and, [18, 14]⟩,
    ⟨.and, [21, 10]⟩,
    ⟨.or, [25, 26]⟩,
    ⟨.and, [24, 13]⟩,
    ⟨.or, [27, 28]⟩], 29⟩

end PEqualNP.Outside.L_meta_10250

theorem PEqualNP.Outside.L_meta_10250 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => decide (((List.ofFn x).count true) % 3 = 0)) 27 := by
  refine ⟨PEqualNP.Outside.L_meta_10250.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_10250.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
