import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3178_1
    (hLower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 15 →
        ¬ ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) =
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
            x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
            x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (hCompose : ∀ (pins : List ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      pins.length = 2 → (∀ i ∈ pins, i < 10) → 0 ∈ pins →
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D ∧ D.size ≤ C.size + 2 ∧
          ∀ x : Fin 9 → Bool,
            D.eval (List.ofFn x) =
              C.eval ((List.ofFn x ++ [!x 0]) ++
                [PEqualNP.CircuitLowerBounds.GateOp.or.eval
                  (pins.map fun i => (List.ofFn x ++ [!x 0]).getD i false)]))
    : ∀ (pins : List ℕ), pins.length = 2 →
      (∀ i ∈ pins, i < 10) → (0 ∈ pins ∨ 9 ∈ pins) →
      (¬ ∀ i ∈ pins, i = 0 ∨ i = 9) ∧ 0 ∈ pins →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          ∃ x : Fin 9 → Bool,
            have u : List Bool := List.ofFn x ++ [!x 0]
            C.eval (u ++
              [PEqualNP.CircuitLowerBounds.GateOp.or.eval
                (pins.map fun i => u.getD i false)]) ≠
              (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
                x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
                x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
  intro pins hlen hbound hor hconditions C hfan hsize
  obtain ⟨D, hDfan, hDsize, hD⟩ :=
    hCompose pins C hlen hbound hconditions.2 hfan hsize
  have hDsize' : D.size ≤ 15 := by omega
  obtain ⟨x, hx⟩ := not_forall.mp (hLower D hDfan hDsize')
  refine ⟨x, ?_⟩
  intro u heq
  apply hx
  rw [hD x]
  exact heq
