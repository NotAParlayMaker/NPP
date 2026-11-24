import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1532 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 := by
  intro n G U x hU K2 hK2 K hK
  classical
  have hcov : G.IsVertexCover ((insert x K2 : Finset (Fin n)) : Set (Fin n)) := by
    intro v w hvw
    by_cases he : s(v, w) ∈ U
    · have hx := hU _ he
      rcases Sym2.mem_iff.mp hx with h | h
      · left
        exact Finset.mem_coe.mpr (h ▸ Finset.mem_insert_self _ _)
      · right
        exact Finset.mem_coe.mpr (h ▸ Finset.mem_insert_self _ _)
    · have hadj : (G.deleteEdges (↑U : Set (Sym2 (Fin n)))).Adj v w := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hvw, fun hmem => he (Finset.mem_coe.mp hmem)⟩
      rcases hK2.1 hadj with h | h
      · left
        exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp h))
      · right
        exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp h))
  have h1 := hK.2 _ hcov
  have h2 : (insert x K2).card ≤ K2.card + 1 := Finset.card_insert_le _ _
  omega
