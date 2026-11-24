import PEqualNP.Defs

-- Reduction of L-meta-2962 (core-cover bound at a lift fixed point), by cases on the
-- maximal cores, following the cases priced in the step's sketch: a core alone;
-- several cores with pairwise disjoint cones; several cores, two sharing a cone gate.
theorem PEqualNP.Outside.R_meta_2962_1 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
      (PEqualNP.Core.maximalCores G C).card ≤ 1 →
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
        ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
      2 ≤ (PEqualNP.Core.maximalCores G C).card →
      (∀ g₁ ∈ (PEqualNP.Core.maximalCores G C), ∀ g₂ ∈ (PEqualNP.Core.maximalCores G C), g₁ ≠ g₂ →
        Disjoint (PEqualNP.Core.coneSet n C g₁) (PEqualNP.Core.coneSet n C g₂)) →
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
        ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
      2 ≤ (PEqualNP.Core.maximalCores G C).card →
      (∃ g₁ ∈ (PEqualNP.Core.maximalCores G C), ∃ g₂ ∈ (PEqualNP.Core.maximalCores G C), g₁ ≠ g₂ ∧
        (PEqualNP.Core.coneSet n C g₁ ∩ PEqualNP.Core.coneSet n C g₂).Nonempty) →
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
        ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
        ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card := by
  intro halone hdisj hshared n G _inst C s T T' hbip hnc hao hfun hfix hT hT'
  by_cases hcard : (PEqualNP.Core.maximalCores G C).card ≤ 1
  · exact halone n G C s T T' hbip hnc hao hfun hfix hT hT' hcard
  · have hcard2 : 2 ≤ (PEqualNP.Core.maximalCores G C).card := by omega
    by_cases hdisjProp : ∀ g₁ ∈ (PEqualNP.Core.maximalCores G C), ∀ g₂ ∈ (PEqualNP.Core.maximalCores G C), g₁ ≠ g₂ →
        Disjoint (PEqualNP.Core.coneSet n C g₁) (PEqualNP.Core.coneSet n C g₂)
    · exact hdisj n G C s T T' hbip hnc hao hfun hfix hT hT' hcard2 hdisjProp
    · push Not at hdisjProp
      obtain ⟨g₁, hg₁, g₂, hg₂, hne, hnd⟩ := hdisjProp
      have hne' : (PEqualNP.Core.coneSet n C g₁ ∩ PEqualNP.Core.coneSet n C g₂).Nonempty := by
        rcases Finset.eq_empty_or_nonempty (PEqualNP.Core.coneSet n C g₁ ∩ PEqualNP.Core.coneSet n C g₂) with hempty | hnon
        · exact absurd (Finset.disjoint_iff_inter_eq_empty.mpr hempty) hnd
        · exact hnon
      exact hshared n G C s T T' hbip hnc hao hfun hfix hT hT' hcard2 ⟨g₁, hg₁, g₂, hg₂, hne, hne'⟩
