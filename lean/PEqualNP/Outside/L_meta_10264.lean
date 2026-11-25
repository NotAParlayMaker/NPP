import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10264

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def témoin : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.and, [0, 5]⟩,
    ⟨.and, [1, 4]⟩, ⟨.and, [0, 3]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩,
    ⟨.or, [6, 7]⟩, ⟨.and, [6, 7]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 14]⟩,
    ⟨.or, [15, 11]⟩, ⟨.and, [15, 11]⟩, ⟨.not, [17]⟩, ⟨.and, [16, 18]⟩], 19⟩

theorem taille : témoin.size = 14 := rfl

theorem portes : FanInTwo témoin := by
  intro g hg
  simp only [témoin, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem sortie : ∀ x : Fin 6 → Bool, témoin.eval (List.ofFn x) =
    Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) *
      (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 2 := by
  decide

end PEqualNP.Outside.L_meta_10264

theorem PEqualNP.Outside.L_meta_10264 : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit ((1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat) * (1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat)) 2) 16 := by
  exact ⟨PEqualNP.Outside.L_meta_10264.témoin, PEqualNP.Outside.L_meta_10264.portes, by decide, PEqualNP.Outside.L_meta_10264.sortie⟩
