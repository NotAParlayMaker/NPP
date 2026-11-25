import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2962_41
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op matches PEqualNP.CircuitLowerBounds.GateOp.or)).card + (PEqualNP.Core.maximalCores G C).card)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T'' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover (SimpleGraph.fromEdgeSet (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T'' → T''.card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op matches PEqualNP.CircuitLowerBounds.GateOp.and)).card) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card := by
  intro n G inst C s T T' hs hC4 hAO hF hLift hT hT'
  classical
  obtain ⟨T'', hT''⟩ : ∃ T'' : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (SimpleGraph.fromEdgeSet (((PEqualNP.Core.maximalCores G C).biUnion
        (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T'' := by
    let K : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet
      (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) :
        Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))
    let S : Finset (Finset (Fin n)) :=
      (Finset.univ : Finset (Finset (Fin n))).filter
        (fun T0 : Finset (Fin n) => K.IsVertexCover (T0 : Set (Fin n)))
    have hne : S.Nonempty := ⟨(Finset.univ : Finset (Fin n)),
      Finset.mem_filter.2 ⟨Finset.mem_univ _,
        fun v _ _ => Or.inl (Finset.mem_coe.2 (Finset.mem_univ v))⟩⟩
    obtain ⟨T0, hT0, hmin⟩ := S.exists_min_image Finset.card hne
    exact ⟨T0, (Finset.mem_filter.1 hT0).2,
      fun T1 hT1 => hmin T1 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT1⟩)⟩
  have hA := h1 n G C s hs hC4 hAO hF hLift
  have hB := h2 n G C s T'' hs hC4 hAO hF hLift hT''
  have hU : (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter
        (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op matches
          PEqualNP.CircuitLowerBounds.GateOp.or)).card +
      (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter
        (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op matches
          PEqualNP.CircuitLowerBounds.GateOp.and)).card ≤
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card := by
    rw [← Finset.card_union_of_disjoint]
    · exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
        (Finset.filter_subset _ _))
    · rw [Finset.disjoint_filter]
      intro j _ ha hb
      revert ha hb
      cases (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op <;> simp
  have hcov : T.card ≤ T'.card + T''.card := by
    refine le_trans (hT.2 (T' ∪ T'') ?_) (Finset.card_union_le _ _)
    intro u v huv
    by_cases he : s(u, v) ∈ ((((PEqualNP.Core.maximalCores G C).biUnion
        (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n))))
    · rcases hT''.1 ((SimpleGraph.fromEdgeSet_adj _).2 ⟨he, G.ne_of_adj huv⟩) with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
    · rcases hT'.1 ((SimpleGraph.deleteEdges_adj).2 ⟨huv, he⟩) with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
  omega
