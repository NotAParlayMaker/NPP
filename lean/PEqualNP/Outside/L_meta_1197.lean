import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_1197 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  let c : Circuit := ⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [8, 3]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [5, 12]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [15, 13]⟩,
    ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨c, ?_, by decide, ?_⟩
  · simp [Monotone2, c]
  · decide +kernel
