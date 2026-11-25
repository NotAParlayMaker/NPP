import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6500_1
    (h1 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), x3.card = (0 : ℕ) → (∀ x4 ∈ x3, ∀ (x6 : Fin x1), x2.Adj x4 x6 → x6 ∈ x3) → (∀ x5 ∈ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → ∃ x7 ⊆ x3, (∀ x8 ∈ x7, ∀ x10 ∈ x7, ¬x2.Adj x8 x10) ∧ (5 : ℕ) * x3.card ≤ (14 : ℕ) * x7.card)
    (h2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), (1 : ℕ) ≤ x3.card → (∀ x4 ∈ x3, ∀ (x6 : Fin x1), x2.Adj x4 x6 → x6 ∈ x3) → (∀ x5 ∈ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → ∃ x7 ⊆ x3, (∀ x8 ∈ x7, ∀ x10 ∈ x7, ¬x2.Adj x8 x10) ∧ (5 : ℕ) * x3.card ≤ (14 : ℕ) * x7.card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)), (∀ x4 ∈ x3, ∀ (x6 : Fin x1), x2.Adj x4 x6 → x6 ∈ x3) → (∀ x5 ∈ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → ∃ x7 ⊆ x3, (∀ x8 ∈ x7, ∀ x10 ∈ x7, ¬x2.Adj x8 x10) ∧ (5 : ℕ) * x3.card ≤ (14 : ℕ) * x7.card := by
  intro x1 x2 x3 hclosed hdeg hgirth
  by_cases h : x3.card = 0
  · exact h1 x1 x2 x3 h hclosed hdeg hgirth
  · have hpos : 1 ≤ x3.card := by omega
    exact h2 x1 x2 x3 hpos hclosed hdeg hgirth
