import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10254

def ckt : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [6] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 7] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 2] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 2] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [10] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 11] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [15] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 16] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 17] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 17] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 15] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 15] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 20] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 20] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [23] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 24] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 21] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 21] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [27] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [26, 28] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [25, 29] }
    ],
    output := 30 }

lemma ckt_eval : ∀ x : Fin 5 → Bool,
    ckt.eval (List.ofFn x) = decide (((List.ofFn x).count true) % 3 = 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_10254

theorem PEqualNP.Outside.L_meta_10254 : PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => decide (((List.ofFn x).count true) % 3 = 0)) 26 := by
  refine ⟨PEqualNP.Outside.L_meta_10254.ckt, ?_, by decide, PEqualNP.Outside.L_meta_10254.ckt_eval⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_10254.ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
