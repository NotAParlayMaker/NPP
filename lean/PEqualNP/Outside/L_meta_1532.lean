import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1532 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 := by
  intro n G U x hx K' hK' K hK
  have hcover : G.IsVertexCover (↑(insert x K') : Set (Fin n)) := by
    intro u v huv
    by_cases he : s(u, v) ∈ U
    · rcases Sym2.mem_iff.mp (hx _ he) with h | h
      · exact Or.inl (Finset.mem_insert.mpr (Or.inl h.symm))
      · exact Or.inr (Finset.mem_insert.mpr (Or.inl h.symm))
    · rcases hK'.1 (SimpleGraph.deleteEdges_adj.mpr ⟨huv, he⟩) with hu | hv
      · exact Or.inl (Finset.mem_insert_of_mem hu)
      · exact Or.inr (Finset.mem_insert_of_mem hv)
  exact (hK.2 _ hcover).trans (Finset.card_insert_le x K')
