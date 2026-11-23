import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1191

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩,
    ⟨.or, [4, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [6, 7]⟩,
    ⟨.and, [2, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩

end PEqualNP.Outside.L_meta_1191

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_1191 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 2 && x 7)) x := by
  refine ⟨PEqualNP.Outside.L_meta_1191.circuit, ?_, ?_, ?_⟩
  · unfold PEqualNP.MetaComplexity.Monotone2 PEqualNP.Outside.L_meta_1191.circuit
    simp
  · decide
  · decide +kernel
