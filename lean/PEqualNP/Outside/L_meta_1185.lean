import PEqualNP.Defs
import Mathlib.Data.Fintype.Pi

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_1185 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
    C.size ≤ 9 ∧ ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) ||
        (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 5 && x 6) || (x 5 && x 7)) x := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩,
      ⟨.or, [2, 4]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [6, 7]⟩,
      ⟨.and, [5, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨circuit, ?_, ?_, ?_⟩
  · simp [circuit, PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide
