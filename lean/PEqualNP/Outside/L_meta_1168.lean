import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1168

open PEqualNP.CircuitLowerBounds

-- The three terms cover the star at zero and the remaining two edges.
private def coverCircuit : Circuit :=
  ⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [8, 3]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [15, 14]⟩
  ], 16⟩

end PEqualNP.Outside.L_meta_1168

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_1168 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1168.coverCircuit, ?_, by decide, by decide⟩
  simp [PEqualNP.Outside.L_meta_1168.coverCircuit, PEqualNP.MetaComplexity.Monotone2]
