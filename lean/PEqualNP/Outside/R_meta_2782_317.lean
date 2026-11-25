import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2782_317
    (hZero : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ),
      (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) →
      (∀ x14 < x4.size, x14 ∉ x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x18 : Finset (Fin x2) → Bool) (x19 : Finset (Fin x2) → Bool), ∀ (x20 x21 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x20 x21) (x2 + x2 + x14) = (x18 x20 && x19 x21)) →
      x5 = ∅ →
      x2 * x1 ≤ (100 : ℕ) * x4.size)
    (hSmall : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ),
      (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) →
      (∀ x14 < x4.size, x14 ∉ x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x18 : Finset (Fin x2) → Bool) (x19 : Finset (Fin x2) → Bool), ∀ (x20 x21 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x20 x21) (x2 + x2 + x14) = (x18 x20 && x19 x21)) →
      x5.Nonempty → x5.card ≤ x2 →
      x2 * x1 ≤ (100 : ℕ) * x4.size)
    (hLarge : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ),
      (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) →
      (∀ x14 < x4.size, x14 ∉ x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x18 : Finset (Fin x2) → Bool) (x19 : Finset (Fin x2) → Bool), ∀ (x20 x21 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x20 x21) (x2 + x2 + x14) = (x18 x20 && x19 x21)) →
      x2 < x5.card → (100 : ℕ) * x5.card < x2 * x1 →
      x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → (∀ x14 < x4.size, x14 ∉ x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x18 : Finset (Fin x2) → Bool) (x19 : Finset (Fin x2) → Bool), ∀ (x20 x21 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x20 x21) (x2 + x2 + x14) = (x18 x20 && x19 x21)) → (100 : ℕ) * x5.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  by_cases hemp : x5 = ∅
  · exact hZero x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 hemp
  · by_cases hle : x5.card ≤ x2
    · exact hSmall x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 (Finset.nonempty_iff_ne_empty.mpr hemp) hle
    · exact hLarge x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 (Nat.lt_of_not_ge hle) h10
