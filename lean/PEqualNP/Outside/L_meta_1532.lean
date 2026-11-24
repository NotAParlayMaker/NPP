import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1532

theorem cover_insert {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n)
    (hU : ∀ e ∈ U, x ∈ e) (K'' : Finset (Fin n))
    (hK'' : (G.deleteEdges (U : Set (Sym2 (Fin n)))).IsVertexCover (K'' : Set (Fin n))) :
    G.IsVertexCover ((insert x K'' : Finset (Fin n)) : Set (Fin n)) := by
  intro v w hvw
  by_cases he : s(v, w) ∈ U
  · have hx := hU _ he
    rw [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · left
      simp
    · right
      simp
  · have hadj : (G.deleteEdges (U : Set (Sym2 (Fin n)))).Adj v w := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hvw, by exact_mod_cast he⟩
    rcases hK'' hadj with h | h
    · left
      simp only [Finset.coe_insert, Set.mem_insert_iff]
      exact Or.inr h
    · right
      simp only [Finset.coe_insert, Set.mem_insert_iff]
      exact Or.inr h

end PEqualNP.Outside.L_meta_1532

theorem PEqualNP.Outside.L_meta_1532 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 := by
  intro n G U x hU K'' hK'' K hK
  calc K.card ≤ (insert x K'').card :=
        hK.2 _ (PEqualNP.Outside.L_meta_1532.cover_insert G U x hU K'' hK''.1)
    _ ≤ K''.card + 1 := Finset.card_insert_le _ _
