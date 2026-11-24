import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_350 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => Bool) g.op true true false (fun _ => true) true) ≤ C.size := by
  intro C
  show C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => Bool) g.op true true false (fun _ => true) true) ≤ C.gates.length
  exact List.countP_le_length
