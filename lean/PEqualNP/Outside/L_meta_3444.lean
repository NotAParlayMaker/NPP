import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3444

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core

def cexC : Circuit :=
  { gates := [
      ⟨GateOp.and, [0, 1]⟩,
      ⟨GateOp.and, [2, 3]⟩,
      ⟨GateOp.and, [4, 5]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [9, 8]⟩,
      ⟨GateOp.and, [10, 0]⟩,
      ⟨GateOp.or, [10, 11]⟩
    ]
    output := 12 }

def cexS : Fin 6 → Bool := fun i => decide (i.val % 2 = 1)

def cexT : Finset (Fin 6) := {⟨2, by omega⟩, ⟨4, by omega⟩}

lemma cex_bip :
    ∀ u v : Fin 6, (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]).Adj u v → cexS u ≠ cexS v := by
  decide

lemma cex_c4 : NoFourCycle (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) := by
  decide

lemma cex_ao2 : IsAO2 6 cexC := by
  decide

lemma cex_fun :
    circuitFun 6 cexC = graphFun (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) ∅ := by
  funext x
  revert x
  decide

lemma cex_lfp : IsLiftFixedPoint (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) cexC := by
  decide

lemma cex_live : ∀ k < cexC.gates.length, InOutputCone 6 cexC k := by
  decide

lemma cex_min :
    IsMinCover
      ((edgeGraph 6 [(0, 1), (2, 3), (4, 5)]).deleteEdges
        (((maximalCores (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) cexC).biUnion
            (gammaE (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) cexC) : Finset (Sym2 (Fin 6))) :
          Set (Sym2 (Fin 6))))
      cexT := by
  decide

lemma cex_fail :
    ¬ ((((maximalCores (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) cexC).biUnion
          (coneSet 6 cexC)).filter (fun w =>
            w ∈ maximalCores (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) cexC ∨
              ((readers 6 cexC w).filter (fun k => InOutputCone 6 cexC k)) ⊆
                (maximalCores (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) cexC).biUnion
                  (coneSet 6 cexC))).card +
        ((edgeGraph 6 [(0, 1), (2, 3), (4, 5)]).edgeFinset \
          (maximalCores (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) cexC).biUnion
            (gammaE (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) cexC)).card +
        cexT.card +
        (maximalCores (edgeGraph 6 [(0, 1), (2, 3), (4, 5)]) cexC).card ≤ cexC.size + 1) := by
  decide

end PEqualNP.Outside.L_meta_3444

theorem PEqualNP.Outside.L_meta_3444 :
    ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro H
  exact PEqualNP.Outside.L_meta_3444.cex_fail
    (H 6 (PEqualNP.EdgeOwnership.edgeGraph 6 [(0, 1), (2, 3), (4, 5)])
      PEqualNP.Outside.L_meta_3444.cexC
      PEqualNP.Outside.L_meta_3444.cexS
      PEqualNP.Outside.L_meta_3444.cexT
      PEqualNP.Outside.L_meta_3444.cex_bip
      PEqualNP.Outside.L_meta_3444.cex_c4
      PEqualNP.Outside.L_meta_3444.cex_ao2
      PEqualNP.Outside.L_meta_3444.cex_fun
      PEqualNP.Outside.L_meta_3444.cex_lfp
      PEqualNP.Outside.L_meta_3444.cex_live
      PEqualNP.Outside.L_meta_3444.cex_min)
