import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1532 :
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 := by
  classical
  intro n G U x hU K' hK' K hK
  have hcover : G.IsVertexCover (↑(insert x K') : Set (Fin n)) := by
    intro a b hab
    by_cases he : s(a, b) ∈ U
    · rcases Sym2.mem_iff.mp (hU _ he) with h | h
      · exact Or.inl (by simp [← h])
      · exact Or.inr (by simp [← h])
    · have hdel : (G.deleteEdges ↑U).Adj a b :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hab, he⟩
      rcases hK'.1 hdel with ha | hb
      · exact Or.inl (Finset.mem_insert_of_mem ha)
      · exact Or.inr (Finset.mem_insert_of_mem hb)
  exact (hK.2 (insert x K') hcover).trans (Finset.card_insert_le _ _)
