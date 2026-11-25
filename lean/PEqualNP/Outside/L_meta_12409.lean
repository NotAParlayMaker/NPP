import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12409_aux

open PEqualNP.CircuitLowerBounds

-- Equality is the OR over a of (left a AND right a); one NOT on top gives inequality.
def C : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩,
    ⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩], 15⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 4 => decide (u ≠ v)) C := by
  decide

end PEqualNP.Outside.L_meta_12409_aux

theorem PEqualNP.Outside.L_meta_12409 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => decide (u ≠ v)) C := by
  exact ⟨PEqualNP.Outside.L_meta_12409_aux.C, PEqualNP.Outside.L_meta_12409_aux.fan, by decide,
    PEqualNP.Outside.L_meta_12409_aux.rep⟩
