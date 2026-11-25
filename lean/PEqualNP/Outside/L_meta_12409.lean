import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_12409 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => decide (u ≠ v)) C := by
  refine ⟨⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩], 15⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
