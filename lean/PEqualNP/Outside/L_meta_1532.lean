import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1532 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 := by
  intro n G U x hU K'' hK'' K hK
  have hc : G.IsVertexCover ((insert x K'' : Finset (Fin n)) : Set (Fin n)) := by
    intro u v huv
    by_cases he : s(u, v) ∈ U
    · have hx := hU _ he
      rcases Sym2.mem_iff.mp hx with h | h
      · left; simp [h]
      · right; simp [h]
    · have hadj : (G.deleteEdges ↑U).Adj u v := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨huv, by simpa using he⟩
      rcases hK''.1 hadj with h | h
      · left; simp at h ⊢; exact Or.inr h
      · right; simp at h ⊢; exact Or.inr h
  exact le_trans (hK.2 _ hc) (Finset.card_insert_le _ _)
