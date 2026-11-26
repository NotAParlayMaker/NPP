import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-17457`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_17457_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin x2 → ℕ), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → Function.Injective x3 → (∀ (x7 : Fin x2), x3 x7 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 x7)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (20 : ℕ) + x2 ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin x2 → ℕ), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → Function.Injective x3 → (∀ (x7 : Fin x2), x3 x7 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 x7)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (20 : ℕ) + x2 ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin x2 → ℕ), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → Function.Injective x3 → (∀ (x7 : Fin x2), x3 x7 < x1.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x3 x7)).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (20 : ℕ) + x2 ≤ x1.size) := by
  classical
  intro h1 h2 x1 x2 x3
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
