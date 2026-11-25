import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-9045`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_9045_1 :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x5 < x4.output → x4.output < x2 + x2 + x4.size → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) → x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ x14 : Fin x2, {x15 ∈ x3 x14 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → x2 * x1 ≤ (100 : ℕ) * x4.size) →
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x5 < x4.output → x4.output < x2 + x2 + x4.size → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) → x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ x14 : Fin x2, {x15 ∈ x3 x14 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → x2 * x1 ≤ (100 : ℕ) * x4.size) →
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x5 < x4.output → x4.output < x2 + x2 + x4.size → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → (x4.wires (PEqualNP.GenericRejection.incidenceInput x13 x14)).getD x5 Bool.false = Bool.false) → x2 * (x1 + (1 : ℕ)) ≤ (2 : ℕ) * ∑ x14 : Fin x2, {x15 ∈ x3 x14 | (x4.wires (PEqualNP.GenericRejection.incidenceInput {x15} {x14})).getD x5 Bool.false = Bool.true}.card → x2 * x1 ≤ (100 : ℕ) * x4.size) := by
  classical
  intro h1 h2 x1 x2 x3 x4 x5
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
