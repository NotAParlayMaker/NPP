import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Every circuit for the order-3 incidence either has an AND gate or has none: the two children
-- below split the search by that property.
theorem PEqualNP.Outside.R_meta_7997_862
    (hasAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x6 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x6)) [((0 : ℕ), (7 : ℕ))] → (∃ (i : ℕ), i < x1.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 i).op = PEqualNP.CircuitLowerBounds.GateOp.and) → False)
    (noAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x6 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x6)) [((0 : ℕ), (7 : ℕ))] → (¬ ∃ (i : ℕ), i < x1.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 i).op = PEqualNP.CircuitLowerBounds.GateOp.and) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x6 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x6)) [((0 : ℕ), (7 : ℕ))] → False := by
  intro x1 hsize hAO hdist hfun hsingle
  by_cases h : ∃ (i : ℕ), i < x1.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 i).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact hasAnd x1 hsize hAO hdist hfun hsingle h
  · exact noAnd x1 hsize hAO hdist hfun hsingle h
