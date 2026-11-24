import Mathlib
import PEqualNP.Defs

-- Reduction of the rest bound at a lift fixed point to two counts: the no-core count
-- (the read-once count on a no-4-cycle graph) and the rest count charged to the gates
-- outside the maximal core cones together with the cone gates the rest reads.
theorem PEqualNP.Outside.R_meta_3443_1
    (hNoCore : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T : Finset (Fin n)),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
      PEqualNP.Core.maximalCores G C = ∅ →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      G.edgeFinset.card + T.card ≤ C.size + 1)
    (hRest : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T : Finset (Fin n)),
      let M : Finset ℕ := PEqualNP.Core.maximalCores G C;
      let D : Finset (Sym2 (Fin n)) := (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C);
      let U : Finset ℕ := (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C);
      let W : Finset ℕ := (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)));
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (D : Set (Sym2 (Fin n)))) T →
      (G.edgeFinset \ D).card + T.card + M.card ≤ ((Finset.range C.gates.length) \ U).card + (U \ W).card + 1) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1 := by
  intro n G _ C s T' hbip h4c hAO2 hcf hlf hoc hmin
  by_cases hM : PEqualNP.Core.maximalCores G C = ∅
  · have hminG : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T' := by
      rw [hM] at hmin
      simp only [Finset.biUnion_empty, Finset.coe_empty, SimpleGraph.deleteEdges_empty] at hmin
      exact hmin
    have key := hNoCore n G C s T' hbip h4c hAO2 hcf hlf hoc hM hminG
    have hW0 : (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card = 0 := by
      rw [hM]
      simp
    have hE : (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card = G.edgeFinset.card := by
      rw [hM]
      simp
    have hMc : (PEqualNP.Core.maximalCores G C).card = 0 := by
      rw [hM]
      simp
    rw [hW0, hE, hMc]
    omega
  · have h2 : (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤
        ((Finset.range C.gates.length) \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C) \ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)))).card + 1 := hRest n G C s T' hbip h4c hAO2 hcf hlf hoc hmin
    have hU : (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C) ⊆ Finset.range C.gates.length := by
      rw [Finset.biUnion_subset]
      intro j hj
      have hjr : j ∈ Finset.range C.gates.length := by
        simp only [PEqualNP.Core.maximalCores, PEqualNP.TopForm.gatesWhere, Finset.mem_filter] at hj
        exact hj.1
      intro x hx
      simp only [PEqualNP.Core.coneSet, Finset.mem_insert, Finset.mem_filter] at hx
      rcases hx with rfl | ⟨hxr, _⟩
      · exact hjr
      · exact hxr
    have hW : (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C) := Finset.filter_subset _ _
    have e1 := Finset.card_sdiff_add_card_eq_card hW
    have e2 := Finset.card_sdiff_add_card_eq_card hU
    have e3 : (Finset.range C.gates.length).card = C.size := by
      simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    omega
