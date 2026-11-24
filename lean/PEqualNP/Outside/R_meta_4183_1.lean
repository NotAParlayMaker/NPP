import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4183_1
    (part : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → x4.size = (PEqualNP.TopForm.tops x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orT x2 x4).card + (PEqualNP.TopForm.orN x2 x4).card)
    (core : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → x2.edgeFinset.card + (PEqualNP.TopForm.centreless x2 x4).card ≤ (PEqualNP.TopForm.orT x2 x4).card + (PEqualNP.TopForm.Ustar x2 x4).card + (1 : ℕ) + (PEqualNP.TopForm.lam x2 x4).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → x2.edgeFinset.card + (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card ≤ x4.size + (PEqualNP.TopForm.Ustar x2 x4).card + (1 : ℕ) := by
  intro x1 x2 x3 x4 hnc hne hleast htop
  have hp := part x1 x2 x4 hnc hne hleast htop
  have hc := core x1 x2 x4 hnc hne hleast htop
  have hTc : (PEqualNP.TopForm.centreless x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hL : (PEqualNP.TopForm.lam x2 x4).card ≤ (PEqualNP.TopForm.orN x2 x4).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hsubc : PEqualNP.TopForm.centreless x2 x4 ⊆ PEqualNP.TopForm.tops x2 x4 :=
    Finset.filter_subset _ _
  have hsubl : PEqualNP.TopForm.lam x2 x4 ⊆ PEqualNP.TopForm.orN x2 x4 :=
    Finset.filter_subset _ _
  have hsub1 : (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card =
      (PEqualNP.TopForm.tops x2 x4).card - (PEqualNP.TopForm.centreless x2 x4).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubc]
  have hsub2 : (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card =
      (PEqualNP.TopForm.orN x2 x4).card - (PEqualNP.TopForm.lam x2 x4).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubl]
  omega
