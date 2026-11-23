import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1190 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [4, 12]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · simp [C, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
  · dsimp only [C]
    decide +kernel
