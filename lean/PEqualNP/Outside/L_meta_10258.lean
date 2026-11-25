import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10258

open PEqualNP.CircuitLowerBounds

-- The carry into bit 2 is the conjunction of inputs 0, 1, 3 and 4.
-- Wire 11 takes its XOR with the product of inputs 1 and 4.
-- Wires 15 and 19 then take the parity of the three contributions to bit 2.
def productBit : Circuit where
  gates := [
    ⟨.and, [0, 5]⟩, ⟨.and, [2, 3]⟩,
    ⟨.and, [1, 4]⟩, ⟨.and, [0, 3]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩,
    ⟨.or, [6, 7]⟩, ⟨.and, [6, 7]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 14]⟩,
    ⟨.or, [15, 11]⟩, ⟨.and, [15, 11]⟩, ⟨.not, [17]⟩, ⟨.and, [16, 18]⟩]
  output := 19

theorem fanIn : PEqualNP.MetaComplexity.FanInTwo productBit := by
  intro g hg
  simp only [productBit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_10258

theorem PEqualNP.Outside.L_meta_10258 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 2) 17 := by
  refine ⟨PEqualNP.Outside.L_meta_10258.productBit, PEqualNP.Outside.L_meta_10258.fanIn, by decide, ?_⟩
  decide +kernel
