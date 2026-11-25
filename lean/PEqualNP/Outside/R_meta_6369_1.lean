import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-6369`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_6369_1 :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : DecidableRel x2.Adj) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsAO2 x1 x4 → (∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) → PEqualNP.ReadK.IsReadK x1 x4 (1 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → ∃ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) ∧ x2.edgeFinset.card + x9.card ≤ x4.size + (1 : ℕ)) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : DecidableRel x2.Adj) (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsAO2 x1 x4 → (∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) → PEqualNP.ReadK.IsReadK x1 x4 (1 : ℕ) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → ∃ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) ∧ x2.edgeFinset.card + x9.card ≤ x4.size + (1 : ℕ)) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsAO2 x1 x4 → (∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) → PEqualNP.ReadK.IsReadK x1 x4 (1 : ℕ) → ∃ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) ∧ x2.edgeFinset.card + x9.card ≤ x4.size + (1 : ℕ)) := by
  classical
  intro h1 h2 x1 x2 x3 x4
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
