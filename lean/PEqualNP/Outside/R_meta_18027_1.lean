import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-18027`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_18027_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x5 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), x6 ∈ PEqualNP.CircuitLowerBounds.fanoLines x7 ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true)) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → False) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x5 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), x6 ∈ PEqualNP.CircuitLowerBounds.fanoLines x7 ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true)) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → False) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (26 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x5 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), x6 ∈ PEqualNP.CircuitLowerBounds.fanoLines x7 ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true)) → False) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
