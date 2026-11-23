import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  let f := fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)
  change HasCircuitSize 6 f s ↔ 5 ≤ s
  constructor
  · -- Lower bound: the function depends on each of its six inputs, so a fan-in two circuit for
    -- it has at least five gates.
    intro hc
    have hd : ∀ i : Fin 6, ∃ x : Fin 6 → Bool, f (Function.update x i (!x i)) ≠ f x := by
      dsimp only [f]
      decide +kernel
    have hs := PEqualNP.MetaComplexity.Helpers.dep_lower 6 f hd s hc
    omega
  · -- Upper bound: x0 AND (x1 OR x2 OR x3), OR (x4 AND x5): five gates.
    intro hs
    let C : Circuit :=
      ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩], 10⟩
    refine ⟨C, ?_, hs, ?_⟩
    · simp [C, FanInTwo]
    · dsimp only [C, f]
      decide +kernel
