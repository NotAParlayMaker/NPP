import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2450_2
    (hZero : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj]
      (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) →
      (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x9 →
        x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) →
      PEqualNP.MetaComplexity.Monotone2 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 →
        PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        x4.size ≤ x9.size) →
      PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 →
      x1 = 0 →
      ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x11 ∧
        PEqualNP.MetaComplexity.circuitFun x1 x11 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
        x11.size ≤ x4.size ∧
        PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧
        ∀ x12 < x11.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x15 : Fin x1) (x16 : Fin x1),
            x2.Adj x15 x16 ∧ PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16)
    (hOne : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj]
      (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) →
      (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x9 →
        x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) →
      PEqualNP.MetaComplexity.Monotone2 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 →
        PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        x4.size ≤ x9.size) →
      PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 →
      x1 = 1 →
      ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x11 ∧
        PEqualNP.MetaComplexity.circuitFun x1 x11 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
        x11.size ≤ x4.size ∧
        PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧
        ∀ x12 < x11.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x15 : Fin x1) (x16 : Fin x1),
            x2.Adj x15 x16 ∧ PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16)
    (hTwo : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj]
      (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) →
      (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x9 →
        x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) →
      PEqualNP.MetaComplexity.Monotone2 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 →
        PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        x4.size ≤ x9.size) →
      PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 →
      2 ≤ x1 →
      ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x11 ∧
        PEqualNP.MetaComplexity.circuitFun x1 x11 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
        x11.size ≤ x4.size ∧
        PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧
        ∀ x12 < x11.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x15 : Fin x1) (x16 : Fin x1),
            x2.Adj x15 x16 ∧ PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj]
      (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) →
      (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x9 →
        x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) →
      PEqualNP.MetaComplexity.Monotone2 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 →
        PEqualNP.MetaComplexity.circuitFun x1 x9 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        x4.size ≤ x9.size) →
      PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x4 →
      ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x11 ∧
        PEqualNP.MetaComplexity.circuitFun x1 x11 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
        x11.size ≤ x4.size ∧
        PEqualNP.EdgeOwnership.HasStarProfile x1 x2 x11 ∧
        ∀ x12 < x11.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x15 : Fin x1) (x16 : Fin x1),
            x2.Adj x15 x16 ∧ PEqualNP.EdgeOwnership.Owns x1 x11 x12 x15 x16 := by
  intro x1 x2 _ x4 h1 h2 h3 h4 h5 h6
  by_cases h0 : x1 = 0
  · exact hZero x1 x2 x4 h1 h2 h3 h4 h5 h6 h0
  · by_cases h1' : x1 = 1
    · exact hOne x1 x2 x4 h1 h2 h3 h4 h5 h6 h1'
    · have h2' : 2 ≤ x1 := by omega
      exact hTwo x1 x2 x4 h1 h2 h3 h4 h5 h6 h2'
