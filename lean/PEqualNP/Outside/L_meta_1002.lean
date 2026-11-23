import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1002_counterexample
open CircuitLowerBounds MetaComplexity

private def circuit : Circuit := ⟨[
  ⟨.or,[0,2]⟩, ⟨.or,[8,5]⟩, ⟨.and,[1,9]⟩,
  ⟨.or,[3,6]⟩, ⟨.and,[2,11]⟩,
  ⟨.or,[0,6]⟩, ⟨.or,[13,7]⟩, ⟨.and,[4,14]⟩,
  ⟨.or,[3,5]⟩, ⟨.and,[7,16]⟩,
  ⟨.or,[10,12]⟩, ⟨.or,[15,17]⟩, ⟨.or,[18,19]⟩],20⟩

theorem counterexample : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13 := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp
  · decide +kernel

end PEqualNP.Outside.L_meta_1002_counterexample

theorem PEqualNP.Outside.L_meta_1002 : ¬ (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13) :=
  fun h => h PEqualNP.Outside.L_meta_1002_counterexample.counterexample
