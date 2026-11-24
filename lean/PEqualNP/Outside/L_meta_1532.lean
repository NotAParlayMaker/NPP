import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1532 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 := by
  intro n G U x through K'' hK'' K hK
  apply (hK.2 (insert x K'') ?_).trans (Finset.card_insert_le x K'')
  intro u v adj
  by_cases deleted : s(u, v) ∈ U
  · rcases Sym2.mem_iff.mp (through _ deleted) with hx | hx
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl hx.symm))
    · exact Or.inr (Finset.mem_insert.mpr (Or.inl hx.symm))
  · have kept : (G.deleteEdges (U : Set (Sym2 (Fin n)))).Adj u v :=
      SimpleGraph.deleteEdges_adj.mpr ⟨adj, deleted⟩
    rcases hK''.1 kept with hu | hv
    · exact Or.inl (Finset.mem_insert_of_mem hu)
    · exact Or.inr (Finset.mem_insert_of_mem hv)
