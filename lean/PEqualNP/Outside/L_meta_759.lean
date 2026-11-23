import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_759

open SimpleGraph

def graph : SimpleGraph (Fin 6) :=
  ((((⊥ ⊔ edge 0 1) ⊔ edge 0 2) ⊔ edge 0 3) ⊔ edge 1 4) ⊔ edge 4 5

lemma add_leaf {V : Type*} {G : SimpleGraph V} {u v : V}
    (ha : G.IsAcyclic) (hne : u ≠ v) (hi : ∀ w, ¬ G.Adj v w) :
    (G ⊔ edge u v).IsAcyclic := by
  apply ha.sup_edge_of_not_reachable
  intro hr
  obtain ⟨p⟩ := hr.symm
  cases p with
  | nil => exact hne rfl
  | cons h p => exact hi _ h

lemma forest : graph.IsAcyclic := by
  unfold graph
  apply add_leaf
  · apply add_leaf
    · apply add_leaf
      · apply add_leaf
        · apply add_leaf
          · exact SimpleGraph.isAcyclic_bot
          · decide
          · simp
        · decide
        · intro w
          fin_cases w <;> simp [SimpleGraph.edge_adj]
      · decide
      · intro w
        fin_cases w <;> simp [SimpleGraph.edge_adj]
    · decide
    · intro w
      fin_cases w <;> simp [SimpleGraph.edge_adj]
  · decide
  · intro w
    fin_cases w <;> simp [SimpleGraph.edge_adj]

end PEqualNP.Outside.L_meta_759

theorem PEqualNP.Outside.L_meta_759 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) s ↔ 6 ≤ s := by
  intro s
  let G := PEqualNP.Outside.L_meta_759.graph
  letI : DecidableRel G.Adj := by
    intro a b
    exact decidable_of_iff
      (((((False ∨ (((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)) ∧ a ≠ b)) ∨
        (((a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)) ∧ a ≠ b)) ∨
        (((a = 0 ∧ b = 3) ∨ (a = 3 ∧ b = 0)) ∧ a ≠ b)) ∨
        (((a = 1 ∧ b = 4) ∨ (a = 4 ∧ b = 1)) ∧ a ≠ b)) ∨
        (((a = 4 ∧ b = 5) ∨ (a = 5 ∧ b = 4)) ∧ a ≠ b))
      (by simp only [G, PEqualNP.Outside.L_meta_759.graph, SimpleGraph.sup_adj,
        SimpleGraph.bot_adj, SimpleGraph.edge_adj])
  have he : ∃ i j : Fin 6, G.Adj i j := ⟨0, 1, by decide⟩
  have hc : G.edgeFinset.card = 5 := by decide
  have hcover : ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 4} : Finset (Fin 6)) ∨ j ∈ ({0, 4} : Finset (Fin 6)) := by
    decide
  have hlower : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
    intro T hT
    have h02 := hT 0 2 (by decide)
    have h45 := hT 4 5 (by decide)
    rcases h02 with h0 | h2 <;> rcases h45 with h4 | h5
    · exact Finset.card_le_card (show ({0, 4} : Finset (Fin 6)) ⊆ T by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro h0 h4)
    · exact Finset.card_le_card (show ({0, 5} : Finset (Fin 6)) ⊆ T by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro h0 h5)
    · exact Finset.card_le_card (show ({2, 4} : Finset (Fin 6)) ⊆ T by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro h2 h4)
    · exact Finset.card_le_card (show ({2, 5} : Finset (Fin 6)) ⊆ T by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro h2 h5)
  have hfun : (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) =
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) := by
    decide
  constructor
  · intro h
    rw [← hfun] at h
    have hb := PEqualNP.MetaComplexity.L104 6 2 s G PEqualNP.Outside.L_meta_759.forest he hlower h
    omega
  · intro hs
    have hb := PEqualNP.MetaComplexity.L105 6 G ({0, 4} : Finset (Fin 6)) he hcover
    rw [hc] at hb
    norm_num at hb
    rw [hfun] at hb
    obtain ⟨C, hC, hsize, heval⟩ := hb
    exact ⟨C, hC, hsize.trans hs, heval⟩
