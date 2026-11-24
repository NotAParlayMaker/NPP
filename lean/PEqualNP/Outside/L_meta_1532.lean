import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1532 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 := by
  intro n G U x hx K'' hK'' K hK
  have hcover : G.IsVertexCover (↑(insert x K'') : Set (Fin n)) := by
    intro v w hvw
    by_cases hmem : s(v, w) ∈ (U : Set (Sym2 (Fin n)))
    · have hxvw : x ∈ s(v, w) := hx _ (Finset.mem_coe.mp hmem)
      rw [Sym2.mem_iff] at hxvw
      rcases hxvw with rfl | rfl
      · left
        exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
      · right
        exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)
    · have hdel : (G.deleteEdges (↑U : Set (Sym2 (Fin n)))).Adj v w :=
        (SimpleGraph.deleteEdges_adj).2 ⟨hvw, hmem⟩
      rcases hK''.1 hdel with hv | hw
      · left
        exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hv))
      · right
        exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hw))
  exact (hK.2 (insert x K'') hcover).trans (Finset.card_insert_le x K'')
