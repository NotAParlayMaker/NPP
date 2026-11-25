import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5244_317
    (hClean : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 →
        PEqualNP.TopForm.TopForm x3 x7 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) →
        (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
        PEqualNP.TopForm.centreless x3 x7 = ∅ →
        PEqualNP.TopForm.mixing x3 x7 = ∅ →
        (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)))
    (hCentreless : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 →
        PEqualNP.TopForm.TopForm x3 x7 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) →
        (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
        (PEqualNP.TopForm.centreless x3 x7).Nonempty →
        (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)))
    (hMixing : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x3 x7 →
        PEqualNP.TopForm.TopForm x3 x7 →
        (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card →
        (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) →
        (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) →
        PEqualNP.TopForm.centreless x3 x7 = ∅ →
        (PEqualNP.TopForm.mixing x3 x7).Nonempty →
        (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c1, hc1⟩ := hClean
  obtain ⟨c2, hc2⟩ := hCentreless
  obtain ⟨c3, hc3⟩ := hMixing
  refine ⟨max c1 (max c2 c3), ?_⟩
  intro x2 x3 _ hgirth hedge x7 hleast htop hjunk hcone hnocov
  by_cases hc : PEqualNP.TopForm.centreless x3 x7 = ∅
  · by_cases hm : PEqualNP.TopForm.mixing x3 x7 = ∅
    · exact le_trans (hc1 x2 x3 hgirth hedge x7 hleast htop hjunk hcone hnocov hc hm)
        (Nat.mul_le_mul_right _ (le_max_left c1 (max c2 c3)))
    · exact le_trans (hc3 x2 x3 hgirth hedge x7 hleast htop hjunk hcone hnocov hc (Finset.nonempty_iff_ne_empty.mpr hm))
        (Nat.mul_le_mul_right _ (le_trans (le_max_right c2 c3) (le_max_right c1 (max c2 c3))))
  · exact le_trans (hc2 x2 x3 hgirth hedge x7 hleast htop hjunk hcone hnocov (Finset.nonempty_iff_ne_empty.mpr hc))
      (Nat.mul_le_mul_right _ (le_trans (le_max_left c2 c3) (le_max_right c1 (max c2 c3))))
