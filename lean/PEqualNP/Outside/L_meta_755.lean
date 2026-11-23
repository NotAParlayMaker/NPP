import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755

open SimpleGraph PEqualNP.MetaComplexity

def G₀ : SimpleGraph (Fin 6) := ⊥
def G₁ : SimpleGraph (Fin 6) := G₀ ⊔ edge 1 0
def G₂ : SimpleGraph (Fin 6) := G₁ ⊔ edge 2 0
def G₃ : SimpleGraph (Fin 6) := G₂ ⊔ edge 3 0
def G : SimpleGraph (Fin 6) := G₃ ⊔ edge 5 4

def adjDec (i j : Fin 6) : Decidable (G.Adj i j) :=
  decidable_of_iff
    (((((i = 1 ∧ j = 0 ∨ i = 0 ∧ j = 1) ∧ i ≠ j) ∨
        ((i = 2 ∧ j = 0 ∨ i = 0 ∧ j = 2) ∧ i ≠ j)) ∨
        ((i = 3 ∧ j = 0 ∨ i = 0 ∧ j = 3) ∧ i ≠ j)) ∨
        ((i = 5 ∧ j = 4 ∨ i = 4 ∧ j = 5) ∧ i ≠ j))
    (by simp only [G, G₃, G₂, G₁, G₀, sup_adj, bot_adj, false_or, edge_adj])

lemma isolated {H : SimpleGraph (Fin 6)} {u v : Fin 6}
    (hne : u ≠ v) (hi : ∀ w, ¬ H.Adj u w) : ¬ H.Reachable u v := by
  rintro ⟨p⟩
  cases p with
  | nil => exact hne rfl
  | cons h _ => exact hi _ h

lemma acyclic : G.IsAcyclic := by
  have a₀ : G₀.IsAcyclic := isAcyclic_bot
  have a₁ : G₁.IsAcyclic := a₀.sup_edge_of_not_reachable (isolated
    (show (1 : Fin 6) ≠ 0 by decide) (show ∀ w, ¬ G₀.Adj 1 w by unfold G₀; decide))
  have a₂ : G₂.IsAcyclic := a₁.sup_edge_of_not_reachable (isolated
    (show (2 : Fin 6) ≠ 0 by decide) (show ∀ w, ¬ G₁.Adj 2 w by intro w; fin_cases w <;> simp [G₁, G₀, edge_adj]))
  have a₃ : G₃.IsAcyclic := a₂.sup_edge_of_not_reachable (isolated
    (show (3 : Fin 6) ≠ 0 by decide) (show ∀ w, ¬ G₂.Adj 3 w by intro w; fin_cases w <;> simp [G₂, G₁, G₀, edge_adj]))
  exact a₃.sup_edge_of_not_reachable (isolated
    (show (5 : Fin 6) ≠ 4 by decide) (show ∀ w, ¬ G₃.Adj 5 w by intro w; fin_cases w <;> simp [G₃, G₂, G₁, G₀, edge_adj]))

lemma leftEdge : G.Adj 0 1 := by
  exact @of_decide_eq_true _ (adjDec _ _) rfl

lemma rightEdge : G.Adj 4 5 := by
  exact @of_decide_eq_true _ (adjDec _ _) rfl

lemma coverLower (T : Finset (Fin 6))
    (h : ∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T) : 2 ≤ T.card := by
  have left := h 0 1 leftEdge
  have right := h 4 5 rightEdge
  apply Finset.one_lt_card.mpr
  rcases left with h0 | h1 <;> rcases right with h4 | h5
  · exact ⟨0, h0, 4, h4, by decide⟩
  · exact ⟨0, h0, 5, h5, by decide⟩
  · exact ⟨1, h1, 4, h4, by decide⟩
  · exact ⟨1, h1, 5, h5, by decide⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma exactBound (s : ℕ) :
    HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  let _ : DecidableRel G.Adj := adjDec
  have hfn : ∀ x : Fin 6 → Bool,
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) =
        decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true) := by
    decide
  have he : ∃ i j : Fin 6, G.Adj i j := ⟨0, 1, leftEdge⟩
  have hecount : G.edgeFinset.card = 4 := by decide
  let T : Finset (Fin 6) := {0, 4}
  have ht : T.card = 2 := by decide
  have hcov : ∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T := by decide
  rw [funext hfn]
  constructor
  · intro h
    have hb := L104 6 2 s G acyclic he coverLower h
    omega
  · intro h
    obtain ⟨C, hC, hsize, heval⟩ := L105 6 G T he hcov
    exact ⟨C, hC, by omega, heval⟩

end PEqualNP.Outside.L_meta_755

theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s :=
  PEqualNP.Outside.L_meta_755.exactBound
