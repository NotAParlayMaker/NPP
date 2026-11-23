import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 5]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_1169

theorem PEqualNP.Outside.L_meta_1169 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 1 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1169.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp [PEqualNP.Outside.L_meta_1169.witness] at hg
    rcases hg with h|h|h|h|h|h|h|h <;> subst g <;> simp
  · intro x
    have xs : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := rfl
    rw [xs]
    simp [PEqualNP.Outside.L_meta_1169.witness, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval,
      List.getD, Bool.and_or_distrib_left, Bool.or_assoc]
