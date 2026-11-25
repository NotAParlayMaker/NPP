import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4185_371
    (hCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ K : Finset (Fin n),
          PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G D)) K ∧
            K.card ≤ (PEqualNP.TopForm.tops G D \ PEqualNP.TopForm.centreless G D).card)
    (hCharge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ X : Finset (Fin n), (∀ e ∈ PEqualNP.TopForm.Ustar G D, ∃ v ∈ X, v ∈ e) ∧
          X.card + (PEqualNP.TopForm.Ustar G D).card ≤
            2 * (PEqualNP.TopForm.centreless G D).card + (PEqualNP.TopForm.junk G D).card +
              (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 ∧ x9.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  intro x1 x2 x3 x4 hNF hNE hL hT
  obtain ⟨K, hKcov, hKcard⟩ := hCover x1 x2 x4 hNF hNE hL hT
  obtain ⟨X, hXcov, hXcard⟩ := hCharge x1 x2 x4 hNF hNE hL hT
  refine ⟨K ∪ X, ?_, ?_⟩
  · intro u v huv
    by_cases he : s(u, v) ∈ PEqualNP.TopForm.Ustar x2 x4
    · obtain ⟨w, hwX, hw⟩ := hXcov s(u, v) he
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact Or.inl (Finset.mem_union_right K hwX)
      · exact Or.inr (Finset.mem_union_right K hwX)
    · have hdel : (x2.deleteEdges ↑(PEqualNP.TopForm.Ustar x2 x4)).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨huv, by simpa using he⟩
      rcases hKcov u v hdel with hu | hv
      · exact Or.inl (Finset.mem_union_left X hu)
      · exact Or.inr (Finset.mem_union_left X hv)
  · have h1 : (K ∪ X).card ≤ K.card + X.card := Finset.card_union_le K X
    omega
