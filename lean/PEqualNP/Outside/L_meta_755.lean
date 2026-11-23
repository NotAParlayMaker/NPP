import PEqualNP.MetaComplexity.L104

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

set_option maxRecDepth 16384 in
theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  let f := fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)
  change HasCircuitSize 6 f s ↔ 5 ≤ s
  constructor
  · intro h
    have hd : ∀ i : Fin 6, ∃ x : Fin 6 → Bool, f (Function.update x i (!x i)) ≠ f x := by
      intro i
      refine ⟨fun j => decide (j = (![1, 0, 0, 0, 5, 4] : Fin 6 → Fin 6) i), ?_⟩
      revert i
      dsimp only [f]
      decide
    have := PEqualNP.MetaComplexity.Helpers.dep_lower 6 f hd s h
    omega
  · intro h
    let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩], 10⟩
    refine ⟨C, ?_, h, ?_⟩
    · simp [C, FanInTwo]
    · dsimp only [C, f]
      decide
