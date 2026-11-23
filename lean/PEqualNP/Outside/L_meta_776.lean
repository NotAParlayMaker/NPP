import PEqualNP.Defs

set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.L_meta_776 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    C = ({
      gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩],
      output := 11 } : PEqualNP.CircuitLowerBounds.Circuit) →
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 7 ∧
    (∀ x : Fin 5 → Bool, (C.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 5, (u.val, v.val) ∈ ([(0, 1), (0, 4), (1, 2), (2, 3), (3, 4)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  rintro C rfl
  refine ⟨?_, rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩
  · decide
