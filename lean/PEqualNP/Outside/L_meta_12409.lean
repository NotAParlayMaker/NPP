import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12409_aux

open PEqualNP.CircuitLowerBounds

-- The first four gates detect the matching label. On a one-hot pair,
-- complementing their disjunction gives the inequality matrix.
def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩,
    ⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩], 15⟩

end PEqualNP.Outside.L_meta_12409_aux

open PEqualNP.Outside.L_meta_12409_aux

theorem PEqualNP.Outside.L_meta_12409 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => decide (u ≠ v)) C := by
  refine ⟨witness, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  change (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;>
    first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl) | decide +kernel
