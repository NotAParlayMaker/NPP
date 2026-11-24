import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3446
def G : SimpleGraph (Fin 3) where
  Adj u v := (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)
  symm := by constructor; intro u v h; exact Or.symm h
  loopless := by constructor; intro u h; rcases h with ⟨h0,hn⟩ | ⟨h0,hn⟩ <;> exact hn h0
instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable ((u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0)))
def C : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or,[1,2]⟩,⟨.and,[0,3]⟩,⟨.and,[0,4]⟩,
    ⟨.and,[0,3]⟩,⟨.or,[4,5]⟩,⟨.or,[6,7]⟩],8⟩
def T : Finset (Fin 3) := {0}
def Tr : Finset (Fin 3) := ∅
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem bad_bound : ¬ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet 3 C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers 3 C w).filter (fun k => PEqualNP.Core.InOutputCone 3 C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet 3 C))).card + (PEqualNP.Core.maximalCores G C).card + Tr.card) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem counter : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (PEqualNP.Core.maximalCores G C).card + T'.card) := by
  intro h
  apply bad_bound
  apply h 3 G C (fun u => decide (u ≠ 0)) T Tr
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
end PEqualNP.Outside.L_meta_3446
theorem PEqualNP.Outside.L_meta_3446 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (PEqualNP.Core.maximalCores G C).card + T'.card) := PEqualNP.Outside.L_meta_3446.counter
