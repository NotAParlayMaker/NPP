import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2963

theorem minex (Q : PEqualNP.CircuitLowerBounds.Circuit → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hC : Q C) : ∃ D, Q D ∧ D.size ≤ C.size ∧ ∀ D', Q D' → D.size ≤ D'.size := by
  classical
  have hex : ∃ s, ∃ D : PEqualNP.CircuitLowerBounds.Circuit, Q D ∧ D.size = s := ⟨_, C, hC, rfl⟩
  obtain ⟨D, hD, hs⟩ := Nat.find_spec hex
  refine ⟨D, hD, ?_, ?_⟩
  · rw [hs]; exact Nat.find_min' hex ⟨C, hC, rfl⟩
  · intro D' hD'
    rw [hs]; exact Nat.find_min' hex ⟨D', hD', rfl⟩

end PEqualNP.Outside.L_meta_2963

theorem PEqualNP.Outside.L_meta_2963 :
    ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card) := by
  intro n m R _ C _ hC hf
  obtain ⟨D, ⟨h1, h2⟩, hle, hmin⟩ := PEqualNP.Outside.L_meta_2963.minex
    (fun D => PEqualNP.TopForm.IsAO2 (n + m) D ∧ PEqualNP.MetaComplexity.circuitFun (n + m) D = _) C ⟨hC, hf⟩
  exact ⟨D, h1, h2, hle, fun D' h1' h2' => hmin D' ⟨h1', h2'⟩⟩
