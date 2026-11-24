import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3444_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Core

def ceAdj (u v : Fin 6) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨
  (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨
  (u = 2 ∧ v = 4) ∨ (u = 4 ∧ v = 2) ∨
  (u = 2 ∧ v = 5) ∨ (u = 5 ∧ v = 2)

def ceG : SimpleGraph (Fin 6) where
  Adj := ceAdj
  symm := ⟨fun _ _ h => by rcases h with h|h|h|h|h|h|h|h <;> simp [ceAdj, h]⟩
  loopless := ⟨fun _ h => by rcases h with ⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩ <;> cases h⟩

def ceGDec : DecidableRel ceG.Adj := fun u v => by unfold ceG ceAdj; infer_instance

def ceS : Fin 6 → Bool
  | 0 => false
  | 1 => true
  | 2 => false
  | 3 => true
  | 4 => true
  | 5 => true

def ceC : Circuit :=
  { gates :=
      [ { op := GateOp.or,  inputs := [3, 4] }
      , { op := GateOp.or,  inputs := [6, 5] }
      , { op := GateOp.or,  inputs := [0, 7] }
      , { op := GateOp.and, inputs := [8, 0] }
      , { op := GateOp.and, inputs := [9, 1] }
      , { op := GateOp.and, inputs := [2, 7] }
      , { op := GateOp.or,  inputs := [10, 11] } ]
    output := 12 }

def ceT' : Finset (Fin 6) := {2}

theorem main : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro H
  letI : DecidableRel ceG.Adj := ceGDec
  have h1 : ∀ u v : Fin 6, ceG.Adj u v → ceS u ≠ ceS v := by decide
  have h2 : PEqualNP.TopForm.NoFourCycle ceG := by decide
  have h3 : PEqualNP.TopForm.IsAO2 6 ceC := by decide
  have h4 : PEqualNP.MetaComplexity.circuitFun 6 ceC = PEqualNP.MetaComplexity.NestedCover.graphFun ceG ∅ := by
    funext x
    revert x
    decide
  have h5 : PEqualNP.Core.IsLiftFixedPoint ceG ceC := by decide
  have h6 : ∀ k < ceC.gates.length, PEqualNP.Core.InOutputCone 6 ceC k := by decide
  have h7 : PEqualNP.MetaComplexity.NestedCover.IsMinCover (ceG.deleteEdges (((PEqualNP.Core.maximalCores ceG ceC).biUnion (PEqualNP.TopForm.gammaE ceG ceC) : Finset (Sym2 (Fin 6))) : Set (Sym2 (Fin 6)))) ceT' := by
    refine ⟨?_, ?_⟩
    · intro u v huv
      have hcov : ∀ a b : Fin 6, (ceG.deleteEdges (((PEqualNP.Core.maximalCores ceG ceC).biUnion (PEqualNP.TopForm.gammaE ceG ceC) : Finset (Sym2 (Fin 6))) : Set (Sym2 (Fin 6)))).Adj a b → a ∈ ceT' ∨ b ∈ ceT' := by decide
      exact hcov u v huv
    · intro S hS
      by_contra hlt
      have hcard : ceT'.card = 1 := rfl
      have hS0 : S = ∅ := by
        have hzero : S.card = 0 := by omega
        exact Finset.card_eq_zero.mp hzero
      have hadj : (ceG.deleteEdges (((PEqualNP.Core.maximalCores ceG ceC).biUnion (PEqualNP.TopForm.gammaE ceG ceC) : Finset (Sym2 (Fin 6))) : Set (Sym2 (Fin 6)))).Adj 2 3 := by decide
      have hcov := hS hadj
      rw [hS0] at hcov
      simp at hcov
  have hconcl := H 6 ceG ceC ceS ceT' h1 h2 h3 h4 h5 h6 h7
  have hfalse : ¬ ((((PEqualNP.Core.maximalCores ceG ceC).biUnion (PEqualNP.Core.coneSet 6 ceC)).filter (fun w => w ∈ PEqualNP.Core.maximalCores ceG ceC ∨ ((PEqualNP.TopForm.readers 6 ceC w).filter (fun k => PEqualNP.Core.InOutputCone 6 ceC k)) ⊆ (PEqualNP.Core.maximalCores ceG ceC).biUnion (PEqualNP.Core.coneSet 6 ceC))).card + (ceG.edgeFinset \ (PEqualNP.Core.maximalCores ceG ceC).biUnion (PEqualNP.TopForm.gammaE ceG ceC)).card + ceT'.card + (PEqualNP.Core.maximalCores ceG ceC).card ≤ ceC.size + 1) := by decide
  exact hfalse hconcl

end PEqualNP.Outside.L_meta_3444_aux

theorem PEqualNP.Outside.L_meta_3444 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := PEqualNP.Outside.L_meta_3444_aux.main
