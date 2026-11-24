import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2969

open PEqualNP.CircuitLowerBounds

private abbrev graph : SimpleGraph (Fin 2) := ⊤

private def circuit : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 0]⟩, ⟨.and, [2, 1]⟩], 2⟩

private def color (i : Fin 2) : Bool := decide (i = 0)

private lemma coveredEdges :
    (PEqualNP.Core.maximalCores graph circuit).biUnion
      (PEqualNP.TopForm.gammaE graph circuit) = {s(0, 1)} := by
  decide +kernel

private lemma residualCover :
    PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (graph.deleteEdges (((PEqualNP.Core.maximalCores graph circuit).biUnion
        (PEqualNP.TopForm.gammaE graph circuit) : Finset (Sym2 (Fin 2))) :
          Set (Sym2 (Fin 2)))) ∅ := by
  rw [coveredEdges]
  refine ⟨?_, fun T _ => by simp⟩
  intro u v hadj
  obtain ⟨hne, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hadj
  change u ≠ v at hne
  exfalso
  apply hnot
  simp only [Finset.coe_singleton, Set.mem_singleton_iff]
  fin_cases u <;> fin_cases v <;> simp_all [Sym2.eq_swap]

end PEqualNP.Outside.L_meta_2969

open PEqualNP.Outside.L_meta_2969 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_2969 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro h
  have claimed := h 2 graph circuit color ∅
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by funext x; revert x; decide +kernel) (by decide +kernel) residualCover
  revert claimed
  decide +kernel
