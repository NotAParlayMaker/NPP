import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1003

open PEqualNP.CircuitLowerBounds

-- Group the ten edges into four stars centred at vertices 1, 2, 4 and 7.
private def C : Circuit := ⟨[
  ⟨.or, [0, 2]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [1, 9]⟩,
  ⟨.or, [3, 6]⟩, ⟨.and, [2, 11]⟩,
  ⟨.or, [0, 6]⟩, ⟨.and, [4, 13]⟩,
  ⟨.or, [3, 5]⟩, ⟨.or, [15, 4]⟩, ⟨.and, [7, 16]⟩,
  ⟨.or, [10, 12]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_1003

open PEqualNP.Outside.L_meta_1003 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1003 : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13 := by
  refine ⟨C, ?_, by decide, fun x => ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, C]
  · simp [C, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ, List.getD_eq_getElem?_getD]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.or_eq_true]
    tauto
