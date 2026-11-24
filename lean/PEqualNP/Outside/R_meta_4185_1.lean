import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_4185_1
    (centres : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), NoFourCycle G → IsAO2 n C →
      (∀ e ∈ starEdges G C, ∃ v ∈ (tops G C \ centreless G C).biUnion fun a =>
        if (side (n := n) C a 0).card = 1 then side (n := n) C a 0 else side (n := n) C a 1, v ∈ e) ∧
      ((tops G C \ centreless G C).biUnion fun a =>
        if (side (n := n) C a 0).card = 1 then side (n := n) C a 0 else side (n := n) C a 1).card ≤ (tops G C \ centreless G C).card)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit), NoFourCycle G →
      G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      ∃ K : Finset (Fin n), (∀ e ∈ Ustar G C, ∃ v ∈ K, v ∈ e) ∧ K.card + (Ustar G C).card ≤
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card +
          ((tops G C \ centreless G C).card - ((tops G C \ centreless G C).biUnion fun a =>
        if (side (n := n) C a 0).card = 1 then side (n := n) C a 0 else side (n := n) C a 1).card)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 ∧ x9.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  intro x1 x2 x3 x4 hFour hEdges hLeast hTop
  obtain ⟨hstar, hcard⟩ := centres x1 x2 x4 hFour hLeast.1
  obtain ⟨K, hK, hbound⟩ := residual x1 x2 x4 hFour hEdges hLeast hTop
  set ctr : Finset (Fin x1) := (tops x2 x4 \ centreless x2 x4).biUnion fun a =>
    if (side (n := x1) x4 a 0).card = 1 then side (n := x1) x4 a 0 else side (n := x1) x4 a 1 with hctr
  refine ⟨ctr ∪ K, ?_, ?_⟩
  · intro u v huv
    by_cases hs : s(u, v) ∈ starEdges x2 x4
    · obtain ⟨w, hw, hin⟩ := hstar _ hs
      rcases Sym2.mem_iff.mp hin with rfl | rfl
      · exact Or.inl (by simp [hw])
      · exact Or.inr (by simp [hw])
    · have he : s(u, v) ∈ Ustar x2 x4 :=
        Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv, hs⟩
      obtain ⟨w, hw, hin⟩ := hK _ he
      rcases Sym2.mem_iff.mp hin with rfl | rfl
      · exact Or.inl (by simp [hw])
      · exact Or.inr (by simp [hw])
  · have h1 : (ctr ∪ K).card ≤ ctr.card + K.card := Finset.card_union_le _ _
    have h2 : (2 : ℕ) * (centreless x2 x4).card = 2 * (centreless x2 x4).card := rfl
    omega
