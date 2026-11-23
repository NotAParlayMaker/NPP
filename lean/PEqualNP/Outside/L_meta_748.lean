import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_748

theorem fun_eq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, (SimpleGraph.starGraph (0 : Fin 6)).Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  rw [Bool.eq_iff_iff]
  simp only [SimpleGraph.starGraph_adj, decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ((((⟨h0, h⟩ | ⟨h0, h⟩) | ⟨h0, h⟩) | ⟨h0, h⟩) | ⟨h0, h⟩)
    · exact ⟨0, 1, ⟨by decide, Or.inl rfl⟩, h0, h⟩
    · exact ⟨0, 2, ⟨by decide, Or.inl rfl⟩, h0, h⟩
    · exact ⟨0, 3, ⟨by decide, Or.inl rfl⟩, h0, h⟩
    · exact ⟨0, 4, ⟨by decide, Or.inl rfl⟩, h0, h⟩
    · exact ⟨0, 5, ⟨by decide, Or.inl rfl⟩, h0, h⟩
  · rintro ⟨i, j, ⟨hne, rfl | rfl⟩, hi, hj⟩
    · fin_cases j <;> simp_all
    · fin_cases i <;> simp_all

theorem card_eq : (SimpleGraph.starGraph (0 : Fin 6)).edgeFinset.card = 5 := by
  decide

theorem has_edge : ∃ i j : Fin 6, (SimpleGraph.starGraph (0 : Fin 6)).Adj i j :=
  ⟨0, 1, SimpleGraph.starGraph_center_adj (by decide)⟩

theorem cover_bound : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, (SimpleGraph.starGraph (0 : Fin 6)).Adj i j → i ∈ T ∨ j ∈ T) → 1 ≤ T.card := by
  intro T hT
  rcases hT 0 1 (SimpleGraph.starGraph_center_adj (by decide)) with h | h
  · exact Finset.card_pos.mpr ⟨0, h⟩
  · exact Finset.card_pos.mpr ⟨1, h⟩

theorem cover_ok : ∀ i j : Fin 6, (SimpleGraph.starGraph (0 : Fin 6)).Adj i j → i ∈ ({0} : Finset (Fin 6)) ∨ j ∈ ({0} : Finset (Fin 6)) := by
  intro i j h
  rcases (SimpleGraph.starGraph_adj.mp h).2 with h0 | h0
  · exact Or.inl (Finset.mem_singleton.mpr h0)
  · exact Or.inr (Finset.mem_singleton.mpr h0)

end PEqualNP.Outside.L_meta_748

theorem PEqualNP.Outside.L_meta_748 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [PEqualNP.Outside.L_meta_748.fun_eq]
  constructor
  · intro h
    have hb := PEqualNP.MetaComplexity.L104 6 1 s (SimpleGraph.starGraph (0 : Fin 6))
      (SimpleGraph.isAcyclic_starGraph 0) PEqualNP.Outside.L_meta_748.has_edge
      PEqualNP.Outside.L_meta_748.cover_bound h
    rw [PEqualNP.Outside.L_meta_748.card_eq] at hb
    omega
  · intro hs
    have hu := PEqualNP.MetaComplexity.L105 6 (SimpleGraph.starGraph (0 : Fin 6)) {0}
      PEqualNP.Outside.L_meta_748.has_edge PEqualNP.Outside.L_meta_748.cover_ok
    rw [PEqualNP.Outside.L_meta_748.card_eq, Finset.card_singleton] at hu
    obtain ⟨C, h1, h2, h3⟩ := hu
    exact ⟨C, h1, by omega, h3⟩
