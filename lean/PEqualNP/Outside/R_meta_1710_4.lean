import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-1710`: the circuit has a second gate, or it does not; the two
constants are combined by taking their maximum. -/
theorem PEqualNP.Outside.R_meta_1710_4 :
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) (x4 : DecidableRel x3.Adj), (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) => Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) →  (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x7.gates[1]? = Option.some g) → x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ))) →
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) (x4 : DecidableRel x3.Adj), (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) => Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) →  ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x7.gates[1]? = Option.some g) → x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ))) →
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2), x3.degree x5 = (0 : ℕ) ∨ (3 : ℕ) ≤ x3.degree x5) → (∀ (x6 : Fin x2) (x7 : x3.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (PEqualNP.MetaComplexity.circuitFun x2 x7 = fun (x9 : Fin x2 → Bool) => Decidable.decide (∃ (x10 : Fin x2) (x11 : Fin x2), x3.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x3.edgeFinset.card ≤ x1 * (x7.size + (1 : ℕ))) := by
  classical
  rintro ⟨c1, h1⟩ ⟨c2, h2⟩
  refine ⟨max c1 c2, ?_⟩
  intro x2 x3 x4 H1 H2 x7 M F
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x7.gates[1]? = Option.some g)
  · have hb := h1 x2 x3 x4 H1 H2 x7 M F h
    exact le_trans hb (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  · have hb := h2 x2 x3 x4 H1 H2 x7 M F h
    exact le_trans hb (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
