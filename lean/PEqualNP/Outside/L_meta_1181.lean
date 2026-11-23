import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1181

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [6, 13]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [15, 14]⟩], 16⟩

set_option maxHeartbeats 800000 in
theorem keq : ∀ a b d e f g h i : Bool,
    circ.eval [a, b, d, e, f, g, h, i] =
      ((a && b) || (a && d) || (a && e) || (a && f) || (b && g) || (g && h) || (h && i)) := by
  decide

theorem ofFnN (x : Fin 8 → Bool) :
    List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
  simp [List.ofFn_succ]

end PEqualNP.Outside.L_meta_1181

theorem PEqualNP.Outside.L_meta_1181 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 5 && x 6) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1181.circ, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_1181.circ]
  · decide
  · intro x
    rw [PEqualNP.Outside.L_meta_1181.ofFnN]
    exact PEqualNP.Outside.L_meta_1181.keq (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
