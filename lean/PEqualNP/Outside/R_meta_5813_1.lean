import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5813_1
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),
      PEqualNP.MetaComplexity.Monotone2 x1 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →
      (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 →
      (∀ j < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.CleanedNonEdge.OrReaches (27 : ℕ) x1 x1.output j →
        ∀ i < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ¬ PEqualNP.EdgeOwnership.InCone (27 : ℕ) x1 i j) →
      have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];
      (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) →
      (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) →
      (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) →
      (63 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),
      PEqualNP.MetaComplexity.Monotone2 x1 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →
      (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 →
      (∃ j < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.CleanedNonEdge.OrReaches (27 : ℕ) x1 x1.output j ∧
        ∃ i < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone (27 : ℕ) x1 i j) →
      have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];
      (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) →
      (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) →
      (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) →
      (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →       (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 →         have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];         (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) → (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro x1 x2 x3 x4 hm hr hp x8 x9 hPos hQuad hNon
  by_cases h : ∃ j < x1.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt x1 j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      PEqualNP.CleanedNonEdge.OrReaches (27 : ℕ) x1 x1.output j ∧
      ∃ i < x1.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        PEqualNP.EdgeOwnership.InCone (27 : ℕ) x1 i j
  · exact h2 x1 x2 x3 x4 hm hr hp h hPos hQuad hNon
  · refine h1 x1 x2 x3 x4 hm hr hp ?_ hPos hQuad hNon
    intro j hj hop hor i hi hiop hcone
    exact h ⟨j, hj, hop, hor, i, hi, hiop, hcone⟩
