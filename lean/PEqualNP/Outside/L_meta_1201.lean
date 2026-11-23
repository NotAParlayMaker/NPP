import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_1201 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 5 && x 7)) x := by
  let C : Circuit := ⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [8, 3]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [12, 7]⟩,
    ⟨.and, [5, 13]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · intro x
    apply Bool.eq_iff_iff.mpr
    simp [C, Circuit.eval, Circuit.wires, GateOp.eval]
    tauto
