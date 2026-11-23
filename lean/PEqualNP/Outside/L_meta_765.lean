import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_765 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)) s ↔ 5 ≤ s := by
  intro s
  let f : (Fin 6 → Bool) → Bool := fun x => (x 0 && x 1) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 2)
  change HasCircuitSize 6 f s ↔ 5 ≤ s
  constructor
  · intro hc
    have hd : ∀ i : Fin 6, ∃ x : Fin 6 → Bool, f (Function.update x i (!x i)) ≠ f x := by
      dsimp only [f]
      decide +kernel
    have hs' := PEqualNP.MetaComplexity.Helpers.dep_lower 6 f hd s hc
    omega
  · intro hs
    let C : Circuit := ⟨[
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.or, [3, 5]⟩,
      ⟨GateOp.and, [6, 7]⟩,
      ⟨GateOp.and, [0, 1]⟩,
      ⟨GateOp.or, [9, 8]⟩
    ], 10⟩
    refine ⟨C, ?_, hs, ?_⟩
    · simp [C, FanInTwo]
    · dsimp only [C, f]
      decide +kernel
