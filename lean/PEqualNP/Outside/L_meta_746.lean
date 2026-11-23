import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105


namespace PEqualNP.Outside.L_meta_746

abbrev star : SimpleGraph (Fin 4) := SimpleGraph.starGraph (0 : Fin 4)

lemma star_edge : ∃ i j : Fin 4, star.Adj i j := by
  refine ⟨0, 1, ?_⟩
  decide

lemma star_cover (T : Finset (Fin 4))
    (h : ∀ i j : Fin 4, star.Adj i j → i ∈ T ∨ j ∈ T) : 1 ≤ T.card := by
  obtain ⟨i, j, hij⟩ := star_edge
  have hT : i ∈ T ∨ j ∈ T := h i j hij
  have hne : T.Nonempty := by
    rcases hT with hi | hj
    · exact ⟨i, hi⟩
    · exact ⟨j, hj⟩
  simpa using hne.card_pos

lemma star_cover_zero (i j : Fin 4) (h : star.Adj i j) : i ∈ ({0} : Finset (Fin 4)) ∨ j ∈ ({0} : Finset (Fin 4)) := by
  simpa [star] using h.2

lemma star_edges : star.edgeFinset.card = 3 := by
  decide

lemma star_fun :
    (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) =
      (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, star.Adj i j ∧ x i = true ∧ x j = true)) := by
  decide

lemma star_acyclic : star.IsAcyclic := SimpleGraph.isAcyclic_starGraph (0 : Fin 4)

end PEqualNP.Outside.L_meta_746


theorem PEqualNP.Outside.L_meta_746 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) s ↔ 3 ≤ s := by
  intro s
  constructor
  · intro hC
    rw [PEqualNP.Outside.L_meta_746.star_fun] at hC
    have hb := PEqualNP.MetaComplexity.L104 4 1 s PEqualNP.Outside.L_meta_746.star
      PEqualNP.Outside.L_meta_746.star_acyclic PEqualNP.Outside.L_meta_746.star_edge
      PEqualNP.Outside.L_meta_746.star_cover hC
    rw [PEqualNP.Outside.L_meta_746.star_edges] at hb
    omega
  · intro hs
    rw [PEqualNP.Outside.L_meta_746.star_fun]
    have h3 := PEqualNP.MetaComplexity.L105 4 PEqualNP.Outside.L_meta_746.star
      ({0} : Finset (Fin 4)) PEqualNP.Outside.L_meta_746.star_edge
      PEqualNP.Outside.L_meta_746.star_cover_zero
    rw [PEqualNP.Outside.L_meta_746.star_edges] at h3
    norm_num at h3
    obtain ⟨C, hok, hsize, hev⟩ := h3
    exact ⟨C, hok, le_trans hsize hs, hev⟩
