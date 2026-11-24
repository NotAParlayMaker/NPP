import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3444

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Core

/-- The forest with edges 0-2, 1-3, 1-4, 1-5 (points 0, 1; lines 2..5). -/
def G : SimpleGraph (Fin 6) := edgeGraph 6 [(0, 2), (1, 3), (1, 4), (1, 5)]

instance instG : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (edgeGraph 6 [(0, 2), (1, 3), (1, 4), (1, 5)]).Adj)

/-- Eight gates; gate j is wire 6 + j; output wire 13. -/
def C : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [6, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

/-- The side labelling: points true, lines false. -/
def sg : Fin 6 → Bool := fun i => decide (i.val < 2)

set_option maxRecDepth 100000

lemma h1 : ∀ u v : Fin 6, G.Adj u v → sg u ≠ sg v := by decide +kernel
lemma h2 : NoFourCycle G := by decide +kernel
lemma h3 : IsAO2 6 C := by decide +kernel
lemma h4 : circuitFun 6 C = graphFun G ∅ := by funext x; revert x; decide +kernel
lemma h5 : IsLiftFixedPoint G C := by decide +kernel
lemma h6 : ∀ k < C.gates.length, InOutputCone 6 C k := by decide +kernel
lemma mc : maximalCores G C = {5} := by decide +kernel
lemma ge : gammaE G C 5 = {s(0, 2)} := by decide +kernel

lemma hK : G.deleteEdges (((maximalCores G C).biUnion (gammaE G C) : Finset (Sym2 (Fin 6))) :
    Set (Sym2 (Fin 6))) = edgeGraph 6 [(1, 3), (1, 4), (1, 5)] := by
  rw [mc, Finset.singleton_biUnion, ge]
  ext v w
  simp only [SimpleGraph.deleteEdges_adj, Finset.coe_singleton, Set.mem_singleton_iff]
  revert v w
  decide +kernel

lemma h7' : IsMinCover (edgeGraph 6 [(1, 3), (1, 4), (1, 5)]) ({1} : Finset (Fin 6)) := by
  decide +kernel

lemma h7 : IsMinCover (G.deleteEdges (((maximalCores G C).biUnion (gammaE G C) :
    Finset (Sym2 (Fin 6))) : Set (Sym2 (Fin 6)))) ({1} : Finset (Fin 6)) := by
  rw [hK]
  exact h7'

end PEqualNP.Outside.L_meta_3444

theorem PEqualNP.Outside.L_meta_3444 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro H
  have := H 6 PEqualNP.Outside.L_meta_3444.G PEqualNP.Outside.L_meta_3444.C
    PEqualNP.Outside.L_meta_3444.sg {1} PEqualNP.Outside.L_meta_3444.h1
    PEqualNP.Outside.L_meta_3444.h2 PEqualNP.Outside.L_meta_3444.h3
    PEqualNP.Outside.L_meta_3444.h4 PEqualNP.Outside.L_meta_3444.h5
    PEqualNP.Outside.L_meta_3444.h6 PEqualNP.Outside.L_meta_3444.h7
  revert this
  decide +kernel
