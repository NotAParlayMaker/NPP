import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-6292`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_6292_1 :
    (∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) (x3 : DecidableRel x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ) (x6 : Finset (Fin x1 × Fin x1)), (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x2 x7 x10 ∧ x2 x8 x10) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ x9 ∈ x5, x9 < x4.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x10 x11 : Fin x1), ¬x2 x10 x11 → ∀ x13 ∈ x5, (PEqualNP.EdgeOwnership.gateVal (x1 + x1) x4 x13 fun (x15 : Fin (x1 + x1)) => Decidable.decide (x15 = Fin.castAdd x1 x10 ∨ x15 = Fin.natAdd x1 x11)) = Bool.false) → (∀ x11 ∈ x6, ∃ x13 ∈ x5, [(1 : ℕ), (1 : ℕ)] ∈ (PEqualNP.ReadK.readVectors x4 (x1 + x1) [↑x11.1, x1 + ↑x11.2] (1 : ℕ)).getD (x1 + x1 + x13) []) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → x6.card ≤ (4 : ℕ) * x4.size) →
    (∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) (x3 : DecidableRel x2) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ) (x6 : Finset (Fin x1 × Fin x1)), (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x2 x7 x10 ∧ x2 x8 x10) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ x9 ∈ x5, x9 < x4.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x10 x11 : Fin x1), ¬x2 x10 x11 → ∀ x13 ∈ x5, (PEqualNP.EdgeOwnership.gateVal (x1 + x1) x4 x13 fun (x15 : Fin (x1 + x1)) => Decidable.decide (x15 = Fin.castAdd x1 x10 ∨ x15 = Fin.natAdd x1 x11)) = Bool.false) → (∀ x11 ∈ x6, ∃ x13 ∈ x5, [(1 : ℕ), (1 : ℕ)] ∈ (PEqualNP.ReadK.readVectors x4 (x1 + x1) [↑x11.1, x1 + ↑x11.2] (1 : ℕ)).getD (x1 + x1 + x13) []) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → x6.card ≤ (4 : ℕ) * x4.size) →
    (∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ) (x6 : Finset (Fin x1 × Fin x1)), (∀ (x7 x8 : Fin x1), x7 ≠ x8 → ∃! x10 : Fin x1, x2 x7 x10 ∧ x2 x8 x10) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ x9 ∈ x5, x9 < x4.size ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x10 x11 : Fin x1), ¬x2 x10 x11 → ∀ x13 ∈ x5, (PEqualNP.EdgeOwnership.gateVal (x1 + x1) x4 x13 fun (x15 : Fin (x1 + x1)) => Decidable.decide (x15 = Fin.castAdd x1 x10 ∨ x15 = Fin.natAdd x1 x11)) = Bool.false) → (∀ x11 ∈ x6, ∃ x13 ∈ x5, [(1 : ℕ), (1 : ℕ)] ∈ (PEqualNP.ReadK.readVectors x4 (x1 + x1) [↑x11.1, x1 + ↑x11.2] (1 : ℕ)).getD (x1 + x1 + x13) []) → x6.card ≤ (4 : ℕ) * x4.size) := by
  classical
  intro h1 h2 x1 x2 x3 x4 x5 x6
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
