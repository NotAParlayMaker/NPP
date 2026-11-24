import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_3446

def G : SimpleGraph (Fin 3) where
  Adj u v := (u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0)
  symm := ⟨fun u v h => by omega⟩
  loopless := ⟨fun u h => by omega⟩

def dG : DecidableRel G.Adj := fun u v => by unfold G; infer_instance

def C : Circuit where
  gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [4, 0]⟩,
    ⟨GateOp.and, [3, 0]⟩, ⟨GateOp.or, [5, 4]⟩, ⟨GateOp.or, [7, 6]⟩]
  output := 8

theorem hD : @PEqualNP.Core.maximalCores 3 G dG C = {2} := by decide

theorem hE : @PEqualNP.TopForm.gammaE 3 G dG C 2 = {s(0, 1), s(0, 2)} := by decide

theorem hU : ((({2} : Finset ℕ).biUnion (PEqualNP.Core.coneSet 3 C)).filter (fun w => w ∈ ({2} : Finset ℕ) ∨ ((PEqualNP.TopForm.readers 3 C w).filter (fun k => PEqualNP.Core.InOutputCone 3 C k)) ⊆ ({2} : Finset ℕ).biUnion (PEqualNP.Core.coneSet 3 C))).card = 1 := by decide

end PEqualNP.Outside.L_meta_3446

theorem PEqualNP.Outside.L_meta_3446 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (PEqualNP.Core.maximalCores G C).card + T'.card) := by
  intro h
  have key := @h 3 PEqualNP.Outside.L_meta_3446.G PEqualNP.Outside.L_meta_3446.dG
    PEqualNP.Outside.L_meta_3446.C (fun i => decide (i = 0)) {0} ∅
  rw [PEqualNP.Outside.L_meta_3446.hD, PEqualNP.Outside.L_meta_3446.hU,
    Finset.singleton_biUnion, PEqualNP.Outside.L_meta_3446.hE] at key
  have h1 : @PEqualNP.MetaComplexity.NestedCover.IsMinCover 3 PEqualNP.Outside.L_meta_3446.G {0} := by
    refine ⟨fun u v huv => ?_, fun T' hT' => ?_⟩
    · simp only [PEqualNP.Outside.L_meta_3446.G] at huv
      simp only [Finset.coe_singleton, Set.mem_singleton_iff, Fin.ext_iff]
      omega
    · by_contra hc
      have h0 : T' = ∅ := Finset.card_eq_zero.mp (by rw [Finset.card_singleton] at hc; omega)
      subst h0
      have h01 := @hT' 0 1 (by simp [PEqualNP.Outside.L_meta_3446.G])
      simp at h01
  have h2 : PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (PEqualNP.Outside.L_meta_3446.G.deleteEdges ((({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))) : Set (Sym2 (Fin 3))))) ∅ := by
    refine ⟨fun u v huv => ?_, fun T' _ => by simp⟩
    rw [SimpleGraph.deleteEdges_adj] at huv
    obtain ⟨ha, hn⟩ := huv
    simp only [PEqualNP.Outside.L_meta_3446.G] at ha
    have k2 : ∀ u v : Fin 3, ((u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0)) →
        s(u, v) ∈ ({s(0, 1), s(0, 2)} : Finset (Sym2 (Fin 3))) := by decide
    exact absurd (Finset.mem_coe.mpr (k2 u v ha)) hn
  have h0 : ∀ u v : Fin 3, PEqualNP.Outside.L_meta_3446.G.Adj u v →
      (fun i : Fin 3 => decide (i = 0)) u ≠ (fun i : Fin 3 => decide (i = 0)) v := by
    have k3 : ∀ u v : Fin 3, ((u.val = 0 ∧ v.val ≠ 0) ∨ (v.val = 0 ∧ u.val ≠ 0)) →
        decide (u = 0) ≠ decide (v = 0) := by decide
    exact k3
  have := key h0 (by decide) (by decide) (by funext x; revert x; decide) (by decide)
    (by decide) h1 h2
  revert this
  decide
