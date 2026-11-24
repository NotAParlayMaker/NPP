import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3775_1
    (h_two : ∃ k1 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C → (PEqualNP.TopForm.junk G C).card = 2 →
        (PEqualNP.TopForm.Ustar G C).card ≤ k1 * (C.size + 1))
    (h_many : ∃ k2 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C → 3 ≤ (PEqualNP.TopForm.junk G C).card →
        (∃ i ∈ PEqualNP.TopForm.junk G C, ∃ j ∈ PEqualNP.TopForm.junk G C,
          PEqualNP.EdgeOwnership.InCone n C i j) →
        (¬ ∃ S : Finset (Fin n), ∃ missed : Finset (Sym2 (Fin n)),
          S.card ≤ 4 ∧ missed.card ≤ C.size + 1 ∧
          ∀ e ∈ PEqualNP.TopForm.Ustar G C, e ∈ missed ∨ ∃ p q : Fin n, e = s(p, q) ∧
            ((∃ z ∈ S, G.Adj p z) ∨ ∃ z ∈ S, G.Adj q z)) →
        (PEqualNP.TopForm.Ustar G C).card ≤ k2 * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k1, h1⟩ := h_two
  obtain ⟨k2, h2⟩ := h_many
  refine ⟨max k1 k2, ?_⟩
  intro n G _ hg hne C hL hT hcard hnest hns
  by_cases h2c : (PEqualNP.TopForm.junk G C).card = 2
  · exact (h1 n G hg hne C hL hT h2c).trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · exact (h2 n G hg hne C hL hT (by omega) hnest hns).trans
      (Nat.mul_le_mul_right _ (le_max_right _ _))
