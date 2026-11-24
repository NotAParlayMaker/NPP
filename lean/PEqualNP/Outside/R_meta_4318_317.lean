import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4318_317
    (cClean : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],
      (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →
      (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) →
      x2.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 →
        PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        (∀ x10 < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ (x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput x13 x13) = Bool.false) →
        (∀ x10 < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ (u v : Fin x1), ¬x2.Adj u v → PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput u v) = Bool.false) →
        ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x2.edgeFinset.card + x11.card ≤ x7.size + (1 : ℕ))
    (cImpure : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],
      (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →
      (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) →
      x2.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 →
        PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        (∀ x10 < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ (x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput x13 x13) = Bool.false) →
        (∃ x10 < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∃ (u v : Fin x1), ¬x2.Adj u v ∧ PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput u v) = Bool.true) →
        ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x2.edgeFinset.card + x11.card ≤ x7.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → x2.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x7 → PEqualNP.MetaComplexity.circuitFun x1 x7 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (∀ x10 < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1), PEqualNP.EdgeOwnership.gateVal x1 x7 x10 (PEqualNP.EdgeOwnership.pairInput x13 x13) = Bool.false) → ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x2.edgeFinset.card + x11.card ≤ x7.size + (1 : ℕ) := by
  intro x1 x2 _ htri hc4 hne x7 hmin hfun hsing
  by_cases hclean : ∀ j < x7.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ (u v : Fin x1), ¬x2.Adj u v → PEqualNP.EdgeOwnership.gateVal x1 x7 j (PEqualNP.EdgeOwnership.pairInput u v) = Bool.false
  · exact cClean x1 x2 htri hc4 hne x7 hmin hfun hsing hclean
  · push_neg at hclean
    obtain ⟨j, hj, hop, u, v, hna, hval⟩ := hclean
    exact cImpure x1 x2 htri hc4 hne x7 hmin hfun hsing ⟨j, hj, hop, u, v, hna, Bool.eq_true_of_not_eq_false hval⟩
