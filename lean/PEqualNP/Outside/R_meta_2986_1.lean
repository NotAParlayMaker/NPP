import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2986_1
    (hSmall :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
        PEqualNP.MetaComplexity.Monotone2 x5 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (x2 + x2) x5 →
        (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) →
        (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) →
        x1 ≤ (299 : ℕ) →
        (2 : ℕ) * x2 ≤ x5.size + (1 : ℕ))
    (hLarge :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (300 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
        (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
        PEqualNP.MetaComplexity.Monotone2 x5 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (x2 + x2) x5 →
        (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) →
        (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) →
        (2 : ℕ) * x2 ≤ x5.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (2 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (x2 + x2) x5 →
      (∀ (x12 x13 : Fin x2), x3 x12 x13 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12 ∨ x15 = Fin.natAdd x2 x13)) = Bool.true) →
      (∀ (x13 : Fin (x2 + x2) → Bool), Fintype.card { x14 : Fin x2 // x13 (Fin.natAdd x2 x14) = Bool.true } ≤ x1 → (¬∃ (x15 : Fin x2) (x16 : Fin x2), x3 x15 x16 ∧ x13 (Fin.castAdd x2 x15) = Bool.true ∧ x13 (Fin.natAdd x2 x16) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x13 = Bool.false) →
      (2 : ℕ) * x2 ≤ x5.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hq hOrder hLines hUnique hMono hReads hAccept hReject
  by_cases hSmallBound : x1 ≤ (299 : ℕ)
  · exact hSmall x1 x2 x3 x5 hq hOrder hLines hUnique hMono hReads hAccept hReject hSmallBound
  · have hLargeBound : (300 : ℕ) ≤ x1 := by omega
    exact hLarge x1 x2 x3 x5 hLargeBound hOrder hLines hUnique hMono hReads hAccept hReject
