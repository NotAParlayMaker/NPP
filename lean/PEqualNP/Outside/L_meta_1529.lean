import Mathlib
import PEqualNP.Defs

def PEqualNP.TopForm.NoFourCycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

namespace PEqualNP.Outside.L_meta_1529

open SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

theorem w_not_in_Q (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {w : Fin n} (hwW : w ∈ W) (hwP : w ∈ P) : w ∉ Q := by
  intro hwQ
  have h := (hW w).1 hwW w hwP w hwQ
  rcases h with h | h | h
  · exact absurd h (SimpleGraph.irrefl G)
  · exact absurd h (SimpleGraph.irrefl G)
  · exact absurd h (SimpleGraph.irrefl G)

theorem w_adj_all_Q (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {w : Fin n} (hwW : w ∈ W) (hwP : w ∈ P) : ∀ q ∈ Q, G.Adj w q := by
  intro q hq
  have h := (hW w).1 hwW w hwP q hq
  rcases h with h | h | h
  · exact h
  · exact absurd h (SimpleGraph.irrefl G)
  · exact G.adj_symm h

theorem w_not_in_P (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {w : Fin n} (hwW : w ∈ W) (hwQ : w ∈ Q) : w ∉ P := by
  intro hwP
  have h := (hW w).1 hwW w hwP w hwQ
  rcases h with h | h | h
  · exact absurd h (SimpleGraph.irrefl G)
  · exact absurd h (SimpleGraph.irrefl G)
  · exact absurd h (SimpleGraph.irrefl G)

theorem w_adj_all_P (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {w : Fin n} (hwW : w ∈ W) (hwQ : w ∈ Q) : ∀ p ∈ P, G.Adj w p := by
  intro p hp
  have h := (hW w).1 hwW p hp w hwQ
  rcases h with h | h | h
  · exact G.adj_symm h
  · exact G.adj_symm h
  · exact absurd h (SimpleGraph.irrefl G)

theorem PQ_adj_W (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {s : Fin n} (hs : s ∈ P ∩ Q) {w : Fin n} (hw : w ∈ W) : G.Adj s w := by
  have hsP : s ∈ P := Finset.mem_of_mem_inter_left hs
  have hsQ : s ∈ Q := Finset.mem_of_mem_inter_right hs
  have h := (hW w).1 hw s hsP s hsQ
  rcases h with h | h | h
  · exact absurd h (SimpleGraph.irrefl G)
  · exact h
  · exact h

theorem PQ_not_W (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    {s : Fin n} (hs : s ∈ P ∩ Q) : s ∉ W := by
  intro hsW
  have hsP : s ∈ P := Finset.mem_of_mem_inter_left hs
  exact w_not_in_Q G P Q W hW hsW hsP (Finset.mem_of_mem_inter_right hs)

theorem W_card_le_one (hC4 : PEqualNP.TopForm.NoFourCycle G) (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w)
    (h2 : 2 ≤ (P ∩ Q).card) : W.card ≤ 1 := by
  by_contra h
  have hW2 : 2 ≤ W.card := by omega
  obtain ⟨w1, w2, hw1, hw2, hneW⟩ := Finset.one_lt_card_iff.1 (by omega : 1 < W.card)
  obtain ⟨s1, s2, hs1, hs2, hneS⟩ := Finset.one_lt_card_iff.1 (by omega : 1 < (P ∩ Q).card)
  have a11 := PQ_adj_W G P Q W hW hs1 hw1
  have a12 := PQ_adj_W G P Q W hW hs1 hw2
  have a21 := PQ_adj_W G P Q W hW hs2 hw1
  have a22 := PQ_adj_W G P Q W hW hs2 hw2
  exact hC4 s1 w1 s2 w2 hneS hneW ⟨a11, G.adj_symm a21, a22, G.adj_symm a12⟩

end PEqualNP.Outside.L_meta_1529

theorem PEqualNP.Outside.L_meta_1529 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) := by
  intro n G _ hC4 P Q W hW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hwW hwP
    exact ⟨PEqualNP.Outside.L_meta_1529.w_not_in_Q G P Q W hW hwW hwP,
      PEqualNP.Outside.L_meta_1529.w_adj_all_Q G P Q W hW hwW hwP⟩
  · intro w hwW hwQ
    exact ⟨PEqualNP.Outside.L_meta_1529.w_not_in_P G P Q W hW hwW hwQ,
      PEqualNP.Outside.L_meta_1529.w_adj_all_P G P Q W hW hwW hwQ⟩
  · intro s hs w hw
    exact PEqualNP.Outside.L_meta_1529.PQ_adj_W G P Q W hW hs hw
  · intro s hs
    exact PEqualNP.Outside.L_meta_1529.PQ_not_W G P Q W hW hs
  · exact PEqualNP.Outside.L_meta_1529.W_card_le_one G hC4 P Q W hW
