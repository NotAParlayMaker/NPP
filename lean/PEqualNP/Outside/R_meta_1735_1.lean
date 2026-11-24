import Mathlib
import PEqualNP.Defs

-- A cut of L-meta-1735 by vertex count: at most 24 vertices, or 25+.

theorem PEqualNP.Outside.R_meta_1735_1
    (small : ∀ (x2 : ℕ), x2 ≤ (24 : ℕ) → ∀ (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ (24 : ℕ) * (x7.size + (1 : ℕ)))
    (large : ∀ (x2 : ℕ), (25 : ℕ) ≤ x2 → ∀ (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ (25 : ℕ) * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ), ∀ (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  refine ⟨(25 : ℕ), ?_⟩
  intro x2 x3 dec hgirth hedge x7 hao htop
  rcases lt_or_ge x2 25 with h | h
  · exact (small x2 (by omega) x3 hgirth hedge x7 hao htop).trans (Nat.mul_le_mul_right _ (by norm_num : (24 : ℕ) ≤ 25))
  · exact large x2 h x3 hgirth hedge x7 hao htop
