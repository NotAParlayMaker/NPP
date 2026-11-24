import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_3444

def G : SimpleGraph (Fin 4) where
  Adj u v := (u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0)
  symm := ⟨fun u v h => by omega⟩
  loopless := ⟨fun u h => by omega⟩

def dG : DecidableRel G.Adj := fun u v => by unfold G; infer_instance

def C : Circuit where
  gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.and, [6, 1]⟩, ⟨GateOp.or, [6, 7]⟩]
  output := 8

theorem hD : @PEqualNP.Core.maximalCores 4 G dG C = {3} := by decide

theorem hE : @PEqualNP.TopForm.gammaE 4 G dG C 3 = {s(0, 1)} := by decide

theorem hU : ((({3} : Finset ℕ).biUnion (PEqualNP.Core.coneSet 4 C)).filter (fun w => w ∈ ({3} : Finset ℕ) ∨ ((PEqualNP.TopForm.readers 4 C w).filter (fun k => PEqualNP.Core.InOutputCone 4 C k)) ⊆ ({3} : Finset ℕ).biUnion (PEqualNP.Core.coneSet 4 C))).card = 3 := by decide

end PEqualNP.Outside.L_meta_3444

theorem PEqualNP.Outside.L_meta_3444 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro h
  have key := @h 4 PEqualNP.Outside.L_meta_3444.G PEqualNP.Outside.L_meta_3444.dG
    PEqualNP.Outside.L_meta_3444.C (fun i => decide (i = 0)) {0}
  rw [PEqualNP.Outside.L_meta_3444.hD, PEqualNP.Outside.L_meta_3444.hU,
    Finset.singleton_biUnion, PEqualNP.Outside.L_meta_3444.hE] at key
  have h2 : PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (PEqualNP.Outside.L_meta_3444.G.deleteEdges ((({s(0, 1)} : Finset (Sym2 (Fin 4))) : Set (Sym2 (Fin 4))))) {0} := by
    refine ⟨fun u v huv => ?_, fun T' hT' => ?_⟩
    · rw [SimpleGraph.deleteEdges_adj] at huv
      obtain ⟨ha, _⟩ := huv
      simp only [PEqualNP.Outside.L_meta_3444.G] at ha
      simp only [Finset.coe_singleton, Set.mem_singleton_iff, Fin.ext_iff]
      omega
    · by_contra hc
      have h0 : T' = ∅ := Finset.card_eq_zero.mp (by rw [Finset.card_singleton] at hc; omega)
      subst h0
      have h02 := @hT' 0 2 (by
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨by simp [PEqualNP.Outside.L_meta_3444.G], ?_⟩
        simp only [Finset.coe_singleton, Set.mem_singleton_iff]
        decide)
      simp at h02
  have h0 : ∀ u v : Fin 4, PEqualNP.Outside.L_meta_3444.G.Adj u v →
      (fun i : Fin 4 => decide (i = 0)) u ≠ (fun i : Fin 4 => decide (i = 0)) v := by
    have k3 : ∀ u v : Fin 4, ((u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0)) →
        decide (u = 0) ≠ decide (v = 0) := by decide
    exact k3
  have := key h0 (by decide) (by decide) (by funext x; revert x; decide) (by decide)
    (by decide) h2
  revert this
  decide
