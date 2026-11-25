import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17170_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or,[0,12]⟩,
  ⟨.or,[1,13]⟩,
  ⟨.or,[2,14]⟩,
  ⟨.or,[3,15]⟩,
  ⟨.or,[4,8]⟩,
  ⟨.or,[5,9]⟩,
  ⟨.or,[6,10]⟩,
  ⟨.or,[7,11]⟩,
  ⟨.or,[20,21]⟩,
  ⟨.or,[22,23]⟩,
  ⟨.or,[21,25]⟩,
  ⟨.or,[20,25]⟩,
  ⟨.or,[24,23]⟩,
  ⟨.or,[24,22]⟩,
  ⟨.and,[16,26]⟩,
  ⟨.and,[17,27]⟩,
  ⟨.and,[18,28]⟩,
  ⟨.and,[19,29]⟩,
  ⟨.or,[30,31]⟩,
  ⟨.or,[32,33]⟩,
  ⟨.or,[34,35]⟩], 36⟩

theorem basis : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
theorem works : Represents (fun u v : Fin 8 => decide (u.val / 4 = v.val / 4 ∧ u.val % 4 ≠ v.val % 4)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_17170_aux

open PEqualNP.Outside.L_meta_17170_aux in
theorem PEqualNP.Outside.L_meta_17170 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => decide (u.val / 4 = v.val / 4 ∧ u.val % 4 ≠ v.val % 4)) 21 := by
  exact ⟨witness,basis,by decide,works⟩
