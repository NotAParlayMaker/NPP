import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7360_1
    (h1 : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)), x4.card = (0 : ℕ) → x4 ⊆ x3 → (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6 ≠ x8 → x6.1 ≠ x8.1 ∧ x6.2 ≠ x8.2) → (∀ x7 ⊆ x3, (∀ x9 ∈ x7, ∀ x11 ∈ x7, x9 ≠ x11 → x9.1 ≠ x11.1 ∧ x9.2 ≠ x11.2) → x7.card ≤ x4.card) → ∃ (x8 : Finset (Fin (x1 + x2))), (∀ x9 ∈ x3, Fin.castAdd x2 x9.1 ∈ x8 ∨ Fin.natAdd x1 x9.2 ∈ x8) ∧ x8.card ≤ x3.card - x4.card)
    (h2 : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)), (1 : ℕ) ≤ x4.card → x4 ⊆ x3 → (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6 ≠ x8 → x6.1 ≠ x8.1 ∧ x6.2 ≠ x8.2) → (∀ x7 ⊆ x3, (∀ x9 ∈ x7, ∀ x11 ∈ x7, x9 ≠ x11 → x9.1 ≠ x11.1 ∧ x9.2 ≠ x11.2) → x7.card ≤ x4.card) → ∃ (x8 : Finset (Fin (x1 + x2))), (∀ x9 ∈ x3, Fin.castAdd x2 x9.1 ∈ x8 ∨ Fin.natAdd x1 x9.2 ∈ x8) ∧ x8.card ≤ x3.card - x4.card) :
    ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)), x4 ⊆ x3 → (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6 ≠ x8 → x6.1 ≠ x8.1 ∧ x6.2 ≠ x8.2) → (∀ x7 ⊆ x3, (∀ x9 ∈ x7, ∀ x11 ∈ x7, x9 ≠ x11 → x9.1 ≠ x11.1 ∧ x9.2 ≠ x11.2) → x7.card ≤ x4.card) → ∃ (x8 : Finset (Fin (x1 + x2))), (∀ x9 ∈ x3, Fin.castAdd x2 x9.1 ∈ x8 ∨ Fin.natAdd x1 x9.2 ∈ x8) ∧ x8.card ≤ x3.card - x4.card := by
  intro x1 x2 x3 x4 hsub hmatch hmax
  by_cases h : x4.card = 0
  · exact h1 x1 x2 x3 x4 h hsub hmatch hmax
  · have hpos : 1 ≤ x4.card := by omega
    exact h2 x1 x2 x3 x4 hpos hsub hmatch hmax
