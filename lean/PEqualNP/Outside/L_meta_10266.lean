import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10266_aux

open PEqualNP.CircuitLowerBounds

-- The six product terms feed two carry majorities. The final OR restores
-- bit 4 on the all-true input, where the carry into column 4 is two.
def circuit : Circuit := ⟨[
    ⟨.and, [0, 5]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.and, [2, 4]⟩,
    ⟨.and, [2, 5]⟩,
    ⟨.and, [0, 3]⟩,
    ⟨.and, [7, 12]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [8, 15]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.and, [18, 20]⟩,
    ⟨.or, [19, 21]⟩,
    ⟨.and, [13, 11]⟩,
    ⟨.or, [11, 22]⟩,
    ⟨.and, [11, 22]⟩,
    ⟨.not, [25]⟩,
    ⟨.and, [24, 26]⟩,
    ⟨.or, [27, 23]⟩
  ], 28⟩

end PEqualNP.Outside.L_meta_10266_aux

theorem PEqualNP.Outside.L_meta_10266 :
    PEqualNP.MetaComplexity.HasCircuitSize 6
    (fun x : Fin 6 → Bool => Nat.testBit
      ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) *
       (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 4) 23 := by
  refine ⟨PEqualNP.Outside.L_meta_10266_aux.circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_10266_aux.circuit]
  · decide +kernel
