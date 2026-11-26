import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18130

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [7, 3]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.and, [10, 8]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [13, 12]⟩, ⟨GateOp.or, [13, 12]⟩, ⟨GateOp.or, [18, 16]⟩, ⟨GateOp.and, [20, 19]⟩, ⟨GateOp.and, [14, 17]⟩, ⟨GateOp.and, [15, 22]⟩, ⟨GateOp.or, [15, 22]⟩, ⟨GateOp.or, [23, 21]⟩, ⟨GateOp.and, [25, 24]⟩], 26⟩

theorem fan : FanInTwo witness := by
  simp [FanInTwo, witness]

theorem ok : ∀ x : Fin 7 → Bool, witness.eval (List.ofFn x) = decide (4 ≤ (List.ofFn x).count true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_18130

theorem PEqualNP.Outside.L_meta_18130 : (PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => decide (4 ≤ (List.ofFn x).count true)) 21) := by
  exact ⟨PEqualNP.Outside.L_meta_18130.witness, PEqualNP.Outside.L_meta_18130.fan, by decide, PEqualNP.Outside.L_meta_18130.ok⟩
