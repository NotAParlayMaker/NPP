import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6238_1
    (h1 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card = (0 : ℕ) → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → ∃ (x7 : Finset (Fin x1)), x7.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card ∧ ∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → s(x8, x9) ∉ PEqualNP.TopForm.Ustar x2 x4 → x8 ∈ x7 ∨ x9 ∈ x7)
    (h2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (1 : ℕ) ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → ∃ (x7 : Finset (Fin x1)), x7.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card ∧ ∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → s(x8, x9) ∉ PEqualNP.TopForm.Ustar x2 x4 → x8 ∈ x7 ∨ x9 ∈ x7) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → ∃ (x7 : Finset (Fin x1)), x7.card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card ∧ ∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → s(x8, x9) ∉ PEqualNP.TopForm.Ustar x2 x4 → x8 ∈ x7 ∨ x9 ∈ x7 := by
  intro x1 x2 x3 x4 hnf hleast
  by_cases h : (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card = 0
  · exact h1 x1 x2 x4 h hnf hleast
  · have hpos : 1 ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card := by omega
    exact h2 x1 x2 x4 hpos hnf hleast
