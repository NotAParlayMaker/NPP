import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1001_aux
open CircuitLowerBounds MetaComplexity

private def circuit : Circuit := ⟨[
  ⟨.or,[1,4]⟩,
  ⟨.or,[9,5]⟩,
  ⟨.and,[0,10]⟩,
  ⟨.or,[2,6]⟩,
  ⟨.and,[1,12]⟩,
  ⟨.or,[2,4]⟩,
  ⟨.or,[14,8]⟩,
  ⟨.and,[3,15]⟩,
  ⟨.or,[2,5]⟩,
  ⟨.and,[7,17]⟩,
  ⟨.or,[6,5]⟩,
  ⟨.and,[8,19]⟩,
  ⟨.or,[11,13]⟩,
  ⟨.or,[21,16]⟩,
  ⟨.or,[22,18]⟩,
  ⟨.or,[23,20]⟩],24⟩

theorem upper_bound : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
  · decide +kernel

end PEqualNP.Outside.L_meta_1001_aux

theorem PEqualNP.Outside.L_meta_1001 : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 := PEqualNP.Outside.L_meta_1001_aux.upper_bound
