import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_746

open PEqualNP.MetaComplexity

abbrev graph : SimpleGraph (Fin 4) := SimpleGraph.starGraph 0

lemma edge_card : graph.edgeFinset.card = 3 := by decide

lemma has_edge : ∃ i j : Fin 4, graph.Adj i j := by decide

lemma cover_lower (T : Finset (Fin 4))
    (h : ∀ i j : Fin 4, graph.Adj i j → i ∈ T ∨ j ∈ T) : 1 ≤ T.card := by
  rcases h 0 1 (by decide) with h0 | h1
  · exact Finset.card_pos.mpr ⟨0, h0⟩
  · exact Finset.card_pos.mpr ⟨1, h1⟩

lemma cover_upper : ∀ i j : Fin 4, graph.Adj i j →
    i ∈ ({0} : Finset (Fin 4)) ∨ j ∈ ({0} : Finset (Fin 4)) := by
  intro i j h
  simpa only [Finset.mem_singleton] using (SimpleGraph.starGraph_adj.mp h).2

lemma eval_eq : ∀ x : Fin 4 → Bool,
    decide (∃ i j : Fin 4, graph.Adj i j ∧ x i = true ∧ x j = true) =
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) := by decide

end PEqualNP.Outside.L_meta_746

theorem PEqualNP.Outside.L_meta_746 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) s ↔ 3 ≤ s := by
  intro s
  constructor
  · intro h
    have h' : PEqualNP.MetaComplexity.HasCircuitSize 4
        (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4,
          PEqualNP.Outside.L_meta_746.graph.Adj i j ∧ x i = true ∧ x j = true)) s := by
      simpa only [PEqualNP.Outside.L_meta_746.eval_eq] using h
    have hb := PEqualNP.MetaComplexity.L104 4 1 s
      PEqualNP.Outside.L_meta_746.graph (SimpleGraph.isAcyclic_starGraph 0)
      PEqualNP.Outside.L_meta_746.has_edge PEqualNP.Outside.L_meta_746.cover_lower h'
    rw [PEqualNP.Outside.L_meta_746.edge_card] at hb
    omega
  · intro hs
    obtain ⟨C, hfan, hsize, heval⟩ := PEqualNP.MetaComplexity.L105 4
      PEqualNP.Outside.L_meta_746.graph {0}
      PEqualNP.Outside.L_meta_746.has_edge PEqualNP.Outside.L_meta_746.cover_upper
    refine ⟨C, hfan, ?_, ?_⟩
    · rw [PEqualNP.Outside.L_meta_746.edge_card, Finset.card_singleton] at hsize
      omega
    · intro x
      exact (heval x).trans (PEqualNP.Outside.L_meta_746.eval_eq x)
