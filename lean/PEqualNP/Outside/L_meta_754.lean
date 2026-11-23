import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_754_aux

def A (i j : Fin 5) : Bool :=
  decide ((i.val = 0 ∧ (j.val = 1 ∨ j.val = 2 ∨ j.val = 3)) ∨ (j.val = 0 ∧ (i.val = 1 ∨ i.val = 2 ∨ i.val = 3)) ∨ (i.val = 1 ∧ j.val = 4) ∨ (i.val = 4 ∧ j.val = 1))

def G : SimpleGraph (Fin 5) where
  Adj i j := A i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance instDec : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (A i j = true))

theorem hfun : (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) = (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  revert x
  decide

theorem hedge : ∃ i j : Fin 5, G.Adj i j := ⟨0, 1, by decide⟩

theorem hcard : G.edgeFinset.card = 4 := by decide

theorem hcover : ∀ i j : Fin 5, G.Adj i j → i ∈ ({0, 1} : Finset (Fin 5)) ∨ j ∈ ({0, 1} : Finset (Fin 5)) := by decide

theorem hmin : ∀ T : Finset (Fin 5), (∀ i j : Fin 5, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by decide

theorem hreach : ∀ v : Fin 5, G.Reachable 0 v := by
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable (show G.Adj 0 1 by decide)) (SimpleGraph.Adj.reachable (show G.Adj 1 4 by decide))

theorem hacyc : G.IsAcyclic := by
  have ht : G.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨⟨fun u v => (hreach u).symm.trans (hreach v)⟩, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcard]
    simp
  exact ht.isAcyclic

end PEqualNP.Outside.L_meta_754_aux

open PEqualNP.Outside.L_meta_754_aux in
theorem PEqualNP.Outside.L_meta_754 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 5 ≤ s := by
  intro s
  rw [hfun]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 5 2 s G hacyc hedge hmin h
    rw [hcard] at this
    omega
  · intro hs
    obtain ⟨C, hC, hsz, hev⟩ := PEqualNP.MetaComplexity.L105 5 G {0, 1} hedge hcover
    refine ⟨C, hC, ?_, hev⟩
    rw [hcard] at hsz
    simp at hsz
    omega
