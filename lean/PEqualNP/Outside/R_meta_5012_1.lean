import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_5012_1
    (hNested : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g h : ℕ),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.junk G C = {g, h} → g ≠ h →
      PEqualNP.EdgeOwnership.InCone n C g h →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n C' ∧
        PEqualNP.MetaComplexity.circuitFun n C' =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        (C'.size < C.size ∨ (C'.size ≤ C.size ∧ (PEqualNP.TopForm.junk G C').card = 1)))
    (hFree : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g h : ℕ),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.junk G C = {g, h} → g ≠ h →
      ¬ PEqualNP.EdgeOwnership.InCone n C g h →
      ¬ PEqualNP.EdgeOwnership.InCone n C h g →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 n C' ∧
        PEqualNP.MetaComplexity.circuitFun n C' =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        (C'.size < C.size ∨ (C'.size ≤ C.size ∧ (PEqualNP.TopForm.junk G C').card = 1))) :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsLeastAO G C → (PEqualNP.TopForm.junk G C).card ≠ 1) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsLeastAO G C → (PEqualNP.TopForm.junk G C).card ≠ 2 := by
  intro rung1 n G instAdj C s hcol hfour hleast hcard
  classical
  obtain ⟨g, h, hgh, hpair⟩ := Finset.card_eq_two.mp hcard
  have finish : ∀ C' : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n C' →
      PEqualNP.MetaComplexity.circuitFun n C' =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      (C'.size < C.size ∨ (C'.size ≤ C.size ∧ (PEqualNP.TopForm.junk G C').card = 1)) →
      False := by
    intro C' hmodel hfn hout
    have hmin := hleast.2.2 C' hmodel hfn
    rcases hout with hlt | ⟨hle, hone⟩
    · omega
    · have hleast' : PEqualNP.TopForm.IsLeastAO G C' :=
        ⟨hmodel, hfn, fun D hD hfD => le_trans hle (hleast.2.2 D hD hfD)⟩
      exact rung1 n G C' s hcol hfour hleast' hone
  by_cases hin : PEqualNP.EdgeOwnership.InCone n C g h
  · obtain ⟨C', h1, h2, h3⟩ :=
      hNested n G C s g h hcol hfour hleast hpair hgh hin
    exact finish C' h1 h2 h3
  · by_cases hin' : PEqualNP.EdgeOwnership.InCone n C h g
    · obtain ⟨C', h1, h2, h3⟩ :=
        hNested n G C s h g hcol hfour hleast (by rw [hpair, Finset.pair_comm]) hgh.symm hin'
      exact finish C' h1 h2 h3
    · obtain ⟨C', h1, h2, h3⟩ :=
        hFree n G C s g h hcol hfour hleast hpair hgh hin hin'
      exact finish C' h1 h2 h3
