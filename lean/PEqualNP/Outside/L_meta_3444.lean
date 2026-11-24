import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3444_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.Core
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def star : SimpleGraph (Fin 4) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm := ⟨by intro u v; exact Or.symm⟩
  loopless := ⟨by intro u; simp⟩

private instance starAdj : DecidableRel star.Adj :=
  fun u v => inferInstanceAs (Decidable ((u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)))

private def shore (v : Fin 4) : Bool := decide (v = 0)

private def exampleCircuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩,
    ⟨.and, [6, 0]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [7, 8]⟩], 9⟩

private def cover : Finset (Fin 4) := {0}
private def maxCores := maximalCores star exampleCircuit
private def deleted := maxCores.biUnion (gammaE star exampleCircuit)
private def cones := maxCores.biUnion (coneSet 4 exampleCircuit)
private def internal := cones.filter (fun w => w ∈ maxCores ∨
  ((readers 4 exampleCircuit w).filter (fun k => InOutputCone 4 exampleCircuit k)) ⊆ cones)

private lemma starBipartite : ∀ u v, star.Adj u v → shore u ≠ shore v := by decide
private lemma starC4 : NoFourCycle star := by decide
private lemma exampleAO2 : IsAO2 4 exampleCircuit := by decide
private lemma exampleComputes : circuitFun 4 exampleCircuit = graphFun star ∅ := by
  funext x
  exact (show ∀ y : Fin 4 → Bool, circuitFun 4 exampleCircuit y = graphFun star ∅ y from by decide) x

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private lemma exampleFixed : IsLiftFixedPoint star exampleCircuit := by decide

private lemma exampleLive : ∀ k < exampleCircuit.gates.length, InOutputCone 4 exampleCircuit k := by
  intro k hk
  change k < 6 at hk
  interval_cases k <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private lemma maximalExact : maxCores = {4} := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private lemma deletedExact : deleted = {s((0 : Fin 4), (1 : Fin 4))} := by
  rw [deleted, maximalExact]
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private lemma internalExact : internal = {0, 1, 2, 4} := by
  have hc : cones = {0, 1, 2, 3, 4} := by
    rw [cones, maximalExact]
    decide
  rw [internal, hc, maximalExact]
  decide

private lemma residualCover : IsMinCover (star.deleteEdges (deleted : Set (Sym2 (Fin 4)))) cover := by
  refine ⟨?_, ?_⟩
  · intro v w hw
    rcases (SimpleGraph.deleteEdges_adj.mp hw).1 with h | h
    · exact Or.inl (by simp [cover, h.1])
    · exact Or.inr (by simp [cover, h.1])
  · intro T hT
    have h02 : (star.deleteEdges (deleted : Set (Sym2 (Fin 4)))).Adj 0 2 := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨by decide, ?_⟩
      rw [deletedExact]
      decide
    have hnonempty : T.Nonempty := by
      rcases hT h02 with h | h
      · exact ⟨0, h⟩
      · exact ⟨2, h⟩
    simpa [cover] using Finset.card_pos.mpr hnonempty

private lemma countFails : ¬ (internal.card + (star.edgeFinset \ deleted).card + cover.card +
    maxCores.card ≤ exampleCircuit.size + 1) := by
  rw [internalExact, maximalExact, deletedExact]
  decide

end PEqualNP.Outside.L_meta_3444_aux

open PEqualNP.Outside.L_meta_3444_aux

theorem PEqualNP.Outside.L_meta_3444 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro h
  exact countFails (h 4 star exampleCircuit shore cover starBipartite starC4 exampleAO2
    exampleComputes exampleFixed exampleLive residualCover)
