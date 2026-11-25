import PEqualNP.Defs

-- One OR gate reading inputs 0 and 3: the wires are the eight inputs, then their OR.
theorem PEqualNP.Outside.L_meta_7121 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (1 : ℕ) ∧ ∀ (x2 : Fin (8 : ℕ) → Bool), x1.eval (List.ofFn x2) = (x2 (0 : Fin (8 : ℕ)) || x2 (3 : Fin (8 : ℕ))) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩], 8⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    exact ⟨by simp, by simp⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x2
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ]
