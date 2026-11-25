import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2872_1
    (h_low : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2))
        (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (∃ v : Fin x1, (x3.filter (fun p : Fin x1 × Fin x2 => p.1 = v)).card ≤ 1) →
        (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 →
          ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →
        PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
        (∀ (x8 : Fin (x1 + x2) → Bool),
          PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 =
            Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧
              x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →
        x4 ⊆ x3 →
        (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →
        (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →
        x3.card + x4.card ≤ x5.size + (1 : ℕ))
    (h_high : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2))
        (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ v : Fin x1, 2 ≤ (x3.filter (fun p : Fin x1 × Fin x2 => p.1 = v)).card) →
        (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 →
          ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →
        PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
        (∀ (x8 : Fin (x1 + x2) → Bool),
          PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 =
            Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧
              x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →
        x4 ⊆ x3 →
        (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →
        (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →
        x3.card + x4.card ≤ x5.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2))
      (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 →
        ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
      (∀ (x8 : Fin (x1 + x2) → Bool),
        PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 =
          Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧
            x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →
      x4 ⊆ x3 →
      (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →
      (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →
      x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hc4 hAO hfun hsub hm1 hm2
  by_cases h : ∃ v : Fin x1, (x3.filter (fun p : Fin x1 × Fin x2 => p.1 = v)).card ≤ 1
  · exact h_low x1 x2 x3 x4 x5 h hc4 hAO hfun hsub hm1 hm2
  · push_neg at h
    exact h_high x1 x2 x3 x4 x5 (fun v => by have := h v; omega) hc4 hAO hfun hsub hm1 hm2
