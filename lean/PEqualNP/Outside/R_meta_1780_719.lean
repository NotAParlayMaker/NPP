import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1780_719
    (hZero : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 →
      (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →
      (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
      PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.univ.image (Fin.natAdd x2)) x5 = (0 : ℕ) →
      x2 * x1 ≤ (100 : ℕ) * x5.size)
    (hSmall : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 →
      (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →
      (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
      (1 : ℕ) ≤ PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.univ.image (Fin.natAdd x2)) x5 →
      PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.univ.image (Fin.natAdd x2)) x5 ≤ x2 →
      x2 * x1 ≤ (100 : ℕ) * x5.size)
    (hMid : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 →
      (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →
      (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
      x2 < PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.univ.image (Fin.natAdd x2)) x5 →
      (100 : ℕ) * PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.univ.image (Fin.natAdd x2)) x5 < x2 * x1 →
      x2 * x1 ≤ (100 : ℕ) * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro x1 x2 x3 _ x5 h1 h2 h3 h4 h5 h6 h7
  set k := PEqualNP.CrossAnd.crossCount (x2 + x2) (Finset.univ.image (Fin.natAdd x2)) x5
  by_cases h0 : k = 0
  · exact hZero x1 x2 x3 x5 h1 h2 h3 h4 h5 h6 h7 h0
  · by_cases hle : k ≤ x2
    · exact hSmall x1 x2 x3 x5 h1 h2 h3 h4 h5 h6 h7 (Nat.pos_of_ne_zero h0) hle
    · by_cases hlt : 100 * k < x2 * x1
      · exact hMid x1 x2 x3 x5 h1 h2 h3 h4 h5 h6 h7 (Nat.lt_of_not_ge hle) hlt
      · have hkle : k ≤ x5.size := by
          have hcard := Finset.card_filter_le (Finset.range x5.gates.length)
            (fun j => PEqualNP.CrossAnd.IsCrossAnd (x2 + x2) (Finset.univ.image (Fin.natAdd x2)) x5 j)
          rw [Finset.card_range] at hcard
          exact hcard
        have hmul : 100 * k ≤ 100 * x5.size := Nat.mul_le_mul_left 100 hkle
        exact le_trans (Nat.le_of_not_lt hlt) hmul
