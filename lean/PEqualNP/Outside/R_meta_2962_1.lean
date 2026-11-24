import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2962_1
    (hNoCore :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
        (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        PEqualNP.Core.IsLiftFixedPoint G C →
        PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
        PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
        (PEqualNP.Core.maximalCores G C).card = (0 : ℕ) →
        ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card)
    (hSomeCore :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
        (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        PEqualNP.Core.IsLiftFixedPoint G C →
        PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
        PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
        (1 : ℕ) ≤ (PEqualNP.Core.maximalCores G C).card →
        ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)),
      (∀ u v : Fin n, G.Adj u v → s u ≠ s v) →
      PEqualNP.TopForm.NoFourCycle G →
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      PEqualNP.Core.IsLiftFixedPoint G C →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover G T →
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' →
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (PEqualNP.Core.maximalCores G C).card + T'.card := by
  intro n G inst C s T T' hBip hNo4 hAO2 hFun hFix hMin hMinDel
  rcases Nat.eq_zero_or_pos (PEqualNP.Core.maximalCores G C).card with h0 | hpos
  · exact hNoCore n G C s T T' hBip hNo4 hAO2 hFun hFix hMin hMinDel h0
  · exact hSomeCore n G C s T T' hBip hNo4 hAO2 hFun hFix hMin hMinDel hpos
