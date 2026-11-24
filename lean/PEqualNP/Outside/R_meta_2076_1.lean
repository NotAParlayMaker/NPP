import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2076_1
    (h1 : ∃ (c : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → (∀ (v : Fin x2), (x8.neighborSet v).ncard ≤ (3 : ℕ)) → x8.edgeSet.ncard ≤ c * (x7.size + (1 : ℕ)))
    (h2 : ∃ (c : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → (∃ (v : Fin x2), 3 < (x8.neighborSet v).ncard) → x8.edgeSet.ncard ≤ c * (x7.size + (1 : ℕ)))
    : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  refine ⟨max c1 c2, fun x2 x3 _ hg hn x7 x8 hA hB hC hD => ?_⟩
  by_cases hd : ∀ v : Fin x2, (x8.neighborSet v).ncard ≤ 3
  · exact Nat.le_trans (hc1 x2 x3 hg hn x7 x8 hA hB hC hD hd)
      (Nat.mul_le_mul (Nat.le_max_left _ _) (Nat.le_refl _))
  · push_neg at hd
    exact Nat.le_trans (hc2 x2 x3 hg hn x7 x8 hA hB hC hD hd)
      (Nat.mul_le_mul (Nat.le_max_right _ _) (Nat.le_refl _))
