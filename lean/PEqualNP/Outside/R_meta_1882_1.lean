import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1882_1
    (hEq2 : ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 →
        PEqualNP.TopForm.TopForm x3 x7 →
        (PEqualNP.TopForm.junk x3 x7).card = (2 : ℕ) →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7,
          PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) →
        (PEqualNP.TopForm.Ustar x3 x7).card ≤ (8 : ℕ) * (x7.size + (1 : ℕ)))
    (hGe3 : ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 →
        PEqualNP.TopForm.TopForm x3 x7 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7,
          PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) →
        (PEqualNP.TopForm.Ustar x3 x7).card ≤ (8 : ℕ) * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  refine ⟨8, ?_⟩
  intro x2 x3 _ hGirth hNonempty x7 hLeast hTop hTwo hCone
  rcases lt_or_ge (PEqualNP.TopForm.junk x3 x7).card (3 : ℕ) with hlt | hge
  · have hEq : (PEqualNP.TopForm.junk x3 x7).card = (2 : ℕ) := by omega
    exact hEq2 x2 x3 hGirth hNonempty x7 hLeast hTop hEq hCone
  · exact hGe3 x2 x3 hGirth hNonempty x7 hLeast hTop hge hCone
