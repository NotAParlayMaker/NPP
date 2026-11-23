import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1208

-- The circuit from the posted sketch: inputs are wires 0 to 7, gate j is wire 8 + j.
def circ : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩], 17⟩

theorem circ_correct : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    circ.eval [b0, b1, b2, b3, b4, b5, b6, b7] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b6) || (b5 && b7)) := by
  decide

end PEqualNP.Outside.L_meta_1208

theorem PEqualNP.Outside.L_meta_1208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1208.circ, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_1208.circ, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by
      simp [List.ofFn_succ]
    rw [hx]
    exact PEqualNP.Outside.L_meta_1208.circ_correct _ _ _ _ _ _ _ _
