import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_350

open PEqualNP.CircuitLowerBounds

theorem countP_le_size (C : Circuit) :
    C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => Bool) g.op true true false (fun _ => true) true) ≤ C.size := by
  unfold Circuit.size
  exact List.countP_le_length

end PEqualNP.Outside.L_meta_350

theorem PEqualNP.Outside.L_meta_350 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    C.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => Bool) g.op true true false (fun _ => true) true) ≤ C.size := by
  intro C
  exact PEqualNP.Outside.L_meta_350.countP_le_size C
