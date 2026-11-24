import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1735_2 (h1 : ∃ k1 : ℕ, (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) → G.edgeFinset.Nonempty → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → PEqualNP.TopForm.andPairs n C = 0 → (PEqualNP.TopForm.Ustar G C).card ≤ k1 * (C.size + (1 : ℕ)))) (h2 : ∃ k2 : ℕ, (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (5 : ℕ) ≤ p.length) → G.edgeFinset.Nonempty → ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → 1 ≤ PEqualNP.TopForm.andPairs n C → (PEqualNP.TopForm.Ustar G C).card ≤ k2 * (C.size + (1 : ℕ)))) : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨max k1 k2, ?_⟩
  intro n G _ hgirth hne C hL hT
  by_cases hpa : PEqualNP.TopForm.andPairs n C = 0
  · exact (hk1 n G hgirth hne C hL hT hpa).trans (Nat.mul_le_mul_right _ (le_max_left k1 k2))
  · have hpos : 1 ≤ PEqualNP.TopForm.andPairs n C := by omega
    exact (hk2 n G hgirth hne C hL hT hpos).trans (Nat.mul_le_mul_right _ (le_max_right k1 k2))
