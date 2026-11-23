import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_748_aux

def G : SimpleGraph (Fin 6) where
  Adj i j := (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)
  symm := ⟨fun i j h => by tauto⟩
  loopless := ⟨fun i h => by rcases h with h | h <;> exact h.2 h.1⟩

instance : DecidableRel G.Adj := fun i j => by
  unfold G
  infer_instance

lemma card : G.edgeFinset.card = 5 := by decide

lemma reach (v : Fin 6) : G.Reachable 0 v := by
  by_cases h : v = 0
  · subst h
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (Or.inl ⟨rfl, h⟩)

lemma acyc : G.IsAcyclic := by
  have h : G.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨?_, ?_⟩
    · have : Nonempty (Fin 6) := ⟨0⟩
      exact SimpleGraph.Connected.mk (fun u v => (reach u).symm.trans (reach v))
    · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, card]
      simp
  exact h.isAcyclic

lemma feq : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  revert x
  decide

end PEqualNP.Outside.L_meta_748_aux

open PEqualNP.Outside.L_meta_748_aux in
theorem PEqualNP.Outside.L_meta_748 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [feq]
  have hE : ∃ i j : Fin 6, G.Adj i j := ⟨0, 1, Or.inl ⟨rfl, by decide⟩⟩
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 1 s G acyc hE (fun T hT => by
      rcases hT 0 1 (Or.inl ⟨rfl, by decide⟩) with h | h
      · exact Finset.card_pos.mpr ⟨_, h⟩
      · exact Finset.card_pos.mpr ⟨_, h⟩) h
    rw [card] at this
    omega
  · intro hs
    have h5 := PEqualNP.MetaComplexity.L105 6 G {0} hE (fun i j h => by
      rcases h with h | h
      · exact Or.inl (Finset.mem_singleton.mpr h.1)
      · exact Or.inr (Finset.mem_singleton.mpr h.1))
    rw [card] at h5
    obtain ⟨C, hC, hsz, hev⟩ := h5
    exact ⟨C, hC, le_trans hsz (by simp; omega), hev⟩
