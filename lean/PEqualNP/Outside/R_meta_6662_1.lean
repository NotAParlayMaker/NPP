import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6662_1
    (h1 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),
      (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * x5 * (x4.size + (1 : ℕ)) →
      (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * x5 * (x4.size + (1 : ℕ)) ∨
      ∃ x8 ⊆ PEqualNP.TopForm.Ustar x2 x4, x5 < x8.card ∧ ∀ x9 ∈ x8, ∀ x11 ∈ x8, x9 ≠ x11 → ∀ x14 ∈ x9, ∀ x16 ∈ x11, ¬x2.Adj x14 x16)
    (h2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),
      (2 : ℕ) * x5 * (x4.size + (1 : ℕ)) < (PEqualNP.TopForm.Ustar x2 x4).card →
      (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →
      PEqualNP.TopForm.IsLeastAO x2 x4 →
      ∃ x8 ⊆ PEqualNP.TopForm.Ustar x2 x4, x5 < x8.card ∧ ∀ x9 ∈ x8, ∀ x11 ∈ x8, x9 ≠ x11 → ∀ x14 ∈ x9, ∀ x16 ∈ x11, ¬x2.Adj x14 x16) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),
      (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (5 : ℕ) ≤ x7.length) →
      PEqualNP.TopForm.IsLeastAO x2 x4 →
      (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * x5 * (x4.size + (1 : ℕ)) ∨
      ∃ x8 ⊆ PEqualNP.TopForm.Ustar x2 x4, x5 < x8.card ∧ ∀ x9 ∈ x8, ∀ x11 ∈ x8, x9 ≠ x11 → ∀ x14 ∈ x9, ∀ x16 ∈ x11, ¬x2.Adj x14 x16 := by
  intro x1 x2 x3 x4 x5 hcycle hleast
  by_cases h : (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * x5 * (x4.size + (1 : ℕ))
  · exact h1 x1 x2 x4 x5 h
  · have hlt : (2 : ℕ) * x5 * (x4.size + (1 : ℕ)) < (PEqualNP.TopForm.Ustar x2 x4).card := by omega
    exact Or.inr (h2 x1 x2 x4 x5 hlt hcycle hleast)
