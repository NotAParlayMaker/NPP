import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10398_aux

open PEqualNP.CircuitLowerBounds

-- Eight compare-exchanges sort groups of three and four Boolean inputs.
-- The final six gates combine the group thresholds for a total of four.
def circuit : Circuit := ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.or, [8, 2]⟩,
    ⟨.and, [8, 2]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.and, [7, 9]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.and, [14, 16]⟩,
    ⟨.or, [19, 18]⟩,
    ⟨.and, [19, 18]⟩,
    ⟨.and, [11, 22]⟩,
    ⟨.and, [12, 21]⟩,
    ⟨.and, [10, 17]⟩,
    ⟨.or, [20, 23]⟩,
    ⟨.or, [24, 25]⟩,
    ⟨.or, [26, 27]⟩
  ], 28⟩

end PEqualNP.Outside.L_meta_10398_aux

theorem PEqualNP.Outside.L_meta_10398 :
    PEqualNP.MetaComplexity.HasCircuitSize 7
      (fun x : Fin 7 → Bool => decide (4 ≤ ((List.ofFn x).count true))) 22 := by
  refine ⟨PEqualNP.Outside.L_meta_10398_aux.circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_10398_aux.circuit]
  · decide +kernel
