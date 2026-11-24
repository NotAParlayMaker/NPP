import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3444_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Core PEqualNP.EdgeOwnership

abbrev star : SimpleGraph (Fin 5) := SimpleGraph.starGraph 0

def color (v : Fin 5) : Bool := decide (v=0)

-- Gate 2 is a shared OR of all leaves. Gate 4 repeats the first leaf.
def circuit : Circuit :=
  ⟨[⟨.or,[1,2]⟩,⟨.or,[3,4]⟩,⟨.or,[5,6]⟩,⟨.and,[7,1]⟩,
    ⟨.and,[0,8]⟩,⟨.and,[0,7]⟩,⟨.or,[9,10]⟩],11⟩

def cover : Finset (Fin 5) := {0}

def coreEdges : Finset (Sym2 (Fin 5)) := (maximalCores star circuit).biUnion (gammaE star circuit)

def coreCones : Finset ℕ := (maximalCores star circuit).biUnion (coneSet 5 circuit)

def chargedCoreGates : Finset ℕ := coreCones.filter fun w=>
  w∈maximalCores star circuit ∨ ((readers 5 circuit w).filter (InOutputCone 5 circuit)) ⊆ coreCones

theorem bipartite : ∀ u v,star.Adj u v → color u≠color v := by decide +kernel
theorem noFour : NoFourCycle star := by decide +kernel
theorem legal : IsAO2 5 circuit := by decide +kernel

set_option maxRecDepth 32000 in
theorem correct : circuitFun 5 circuit=graphFun star ∅ := by
  funext x
  exact (by decide +kernel : ∀ x : Fin 5→Bool,circuitFun 5 circuit x=graphFun star ∅ x) x

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem fixed : IsLiftFixedPoint star circuit := by decide +kernel

theorem allLive : ∀ k<circuit.gates.length, InOutputCone 5 circuit k := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem coreRoot : maximalCores star circuit={4} := by decide +kernel

theorem coveredOnlyFirstLeaf : coreEdges={s(0,1)} := by
  unfold coreEdges
  rw [coreRoot]
  decide +kernel

theorem conesBeforeFilter : coreCones={0,1,2,3,4} := by
  unfold coreCones
  rw [coreRoot]
  decide +kernel

theorem conesAfterFilter : chargedCoreGates={0,1,3,4} := by
  unfold chargedCoreGates
  rw [coreRoot,conesBeforeFilter]
  decide +kernel

theorem otherEdgesCount : (star.edgeFinset\coreEdges).card=3 := by
  rw [coveredOnlyFirstLeaf]
  decide +kernel

theorem remainingCover : IsMinCover (star.deleteEdges (coreEdges : Set (Sym2 (Fin 5)))) cover := by
  have endpoint : ∀ u v,star.Adj u v → u=0∨v=0 := by decide +kernel
  have edge : (star.deleteEdges (coreEdges : Set (Sym2 (Fin 5)))).Adj (0 : Fin 5) 2 := by
    rw [coveredOnlyFirstLeaf,SimpleGraph.deleteEdges_adj]
    decide +kernel
  refine ⟨?_,?_⟩
  · intro u v joined
    have yes := endpoint u v (SimpleGraph.deleteEdges_adj.mp joined).1
    simpa [cover] using yes
  · intro T h
    have hit := h edge
    have nonempty : T.Nonempty := hit.elim (fun h=>⟨0,h⟩) (fun h=>⟨2,h⟩)
    simpa only [cover,Finset.card_singleton] using Nat.succ_le_of_lt (Finset.card_pos.mpr nonempty)

theorem listedQuantities : chargedCoreGates.card=4 ∧
    (star.edgeFinset\coreEdges).card=3 ∧ cover.card=1 ∧ (maximalCores star circuit).card=1 ∧
    circuit.size=7 := by
  rw [conesAfterFilter,otherEdgesCount,coreRoot]
  decide +kernel

theorem literal3443IsFalse : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro bound
  have pays := bound 5 star circuit color cover bipartite noFour legal correct fixed allLive remainingCover
  change chargedCoreGates.card+(star.edgeFinset\coreEdges).card+cover.card+
    (maximalCores star circuit).card≤circuit.size+1 at pays
  obtain ⟨gates,edges,vertices,cores,size⟩ := listedQuantities
  omega

end PEqualNP.Outside.L_meta_3444_aux

theorem PEqualNP.Outside.L_meta_3444 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  exact PEqualNP.Outside.L_meta_3444_aux.literal3443IsFalse
