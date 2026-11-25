import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10262_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bitThree := fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 3

-- The carry from column two is set when its four summands total two or three.
def witness : Circuit := ⟨[
  ⟨.and,[2,3]⟩,
  ⟨.and,[0,5]⟩,
  ⟨.and,[1,4]⟩,
  ⟨.and,[0,3]⟩,
  ⟨.and,[6,7]⟩,
  ⟨.or,[6,7]⟩,
  ⟨.and,[8,9]⟩,
  ⟨.and,[8,11]⟩,
  ⟨.or,[13,12]⟩,
  ⟨.or,[10,14]⟩,
  ⟨.and,[10,12]⟩,
  ⟨.not,[16]⟩,
  ⟨.and,[15,17]⟩,
  ⟨.and,[2,4]⟩,
  ⟨.and,[1,5]⟩,
  ⟨.or,[19,20]⟩,
  ⟨.and,[19,20]⟩,
  ⟨.not,[22]⟩,
  ⟨.and,[21,23]⟩,
  ⟨.or,[18,24]⟩,
  ⟨.and,[18,24]⟩,
  ⟨.not,[26]⟩,
  ⟨.and,[25,27]⟩],28⟩

theorem legal : FanInTwo witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = bitThree x := by
  decide +kernel

theorem size : witness.size = 23 := rfl
end PEqualNP.Outside.L_meta_10262_aux

theorem PEqualNP.Outside.L_meta_10262 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 3) 29 := by
  exact ⟨PEqualNP.Outside.L_meta_10262_aux.witness, PEqualNP.Outside.L_meta_10262_aux.legal, by decide, PEqualNP.Outside.L_meta_10262_aux.correct⟩
