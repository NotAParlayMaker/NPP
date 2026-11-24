import Mathlib
import PEqualNP.Defs

/-- Reduce L-meta-1735 by wide vs narrow junk AND gates: split on whether some
junk AND gate carries at least two edges (its `gammaE` has card ≥ 2) or every
junk AND gate carries at most one edge. In the narrow case the counting is
trivial (each junk gate accounts for at most one Ustar edge, once every Ustar
edge is carried by some junk gate); the wide case isolates the structurally
rich gates whose two operands conspire across two distinct edge-inputs. -/
theorem PEqualNP.Outside.R_meta_1735_8
    (h1 : ∃ k1 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∀ g ∈ PEqualNP.TopForm.junk G C, (PEqualNP.TopForm.gammaE G C g).card ≤ 1) →
        (PEqualNP.TopForm.Ustar G C).card ≤ k1 * (C.size + 1))
    (h2 : ∃ k2 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∃ g ∈ PEqualNP.TopForm.junk G C, 2 ≤ (PEqualNP.TopForm.gammaE G C g).card) →
        (PEqualNP.TopForm.Ustar G C).card ≤ k2 * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨max k1 k2, ?_⟩
  intro n G _ hgirth hne C hL hT
  by_cases hw : ∃ g ∈ PEqualNP.TopForm.junk G C, 2 ≤ (PEqualNP.TopForm.gammaE G C g).card
  · exact (hk2 n G hgirth hne C hL hT hw).trans (Nat.mul_le_mul_right _ (le_max_right k1 k2))
  · push Not at hw
    exact (hk1 n G hgirth hne C hL hT (fun g hg => by have hlt := hw g hg; omega)).trans
      (Nat.mul_le_mul_right _ (le_max_left k1 k2))
