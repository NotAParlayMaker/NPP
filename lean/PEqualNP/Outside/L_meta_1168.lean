import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1168

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.or, [10, 5]⟩,
    ⟨GateOp.and, [0, 11]⟩,
    ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.and, [6, 7]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [15, 14]⟩], 16⟩

end PEqualNP.Outside.L_meta_1168

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_meta_1168 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1168.circuit, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1168.circuit]
  · decide +kernel
  · decide +kernel
