import Mathlib.Combinatorics.SimpleGraph.Star
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_747_aux

abbrev G := SimpleGraph.starGraph (0 : Fin 5)

theorem edge_card : G.edgeFinset.card = 4 := by
  have h := (SimpleGraph.isTree_starGraph (0 : Fin 5)).card_edgeFinset
  change G.edgeFinset.card + 1 = 5 at h
  omega

theorem edge_fn :
    (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) =
    (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  apply funext
  decide

end PEqualNP.Outside.L_meta_747_aux

open PEqualNP.Outside.L_meta_747_aux in
theorem PEqualNP.Outside.L_meta_747 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4)) s ↔ 4 ≤ s := by
  intro s
  rw [edge_fn]
  have h01 : G.Adj 0 1 := by decide
  have he : ∃ i j, G.Adj i j := ⟨0, 1, h01⟩
  constructor
  · intro h
    have lower := PEqualNP.MetaComplexity.L104 5 1 s G (SimpleGraph.isAcyclic_starGraph _) he (by
      intro T hT
      rcases hT 0 1 h01 with hz | ho
      · exact Finset.card_pos.mpr ⟨_, hz⟩
      · exact Finset.card_pos.mpr ⟨_, ho⟩) h
    rw [edge_card] at lower
    omega
  · intro hs
    have upper := PEqualNP.MetaComplexity.L105 5 G {0} he (by
      intro i j hij
      simpa only [Finset.mem_singleton] using (SimpleGraph.starGraph_adj.mp hij).2)
    rw [edge_card, Finset.card_singleton] at upper
    obtain ⟨C, hC, hsize, hfun⟩ := upper
    exact ⟨C, hC, by omega, hfun⟩
