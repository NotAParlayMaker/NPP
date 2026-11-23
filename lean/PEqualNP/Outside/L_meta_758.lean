import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_758_aux

def adjB (i j : Fin 6) : Bool :=
  (i.val == 0 && (j.val == 1 || j.val == 2 || j.val == 3)) ||
  (j.val == 0 && (i.val == 1 || i.val == 2 || i.val == 3)) ||
  (i.val == 1 && (j.val == 4 || j.val == 5)) ||
  (j.val == 1 && (i.val == 4 || i.val == 5))

def G : SimpleGraph (Fin 6) where
  Adj i j := adjB i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (adjB i j = true))

theorem hf : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  revert x
  decide +kernel

theorem hcard : G.edgeFinset.card = 5 := by decide +kernel

theorem hcover : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide +kernel

theorem hT : ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 1} : Finset (Fin 6)) ∨ j ∈ ({0, 1} : Finset (Fin 6)) := by
  decide +kernel

theorem hedge : ∃ i j : Fin 6, G.Adj i j := ⟨0, 1, by decide⟩

theorem hreach : ∀ v : Fin 6, G.Reachable 0 v := by
  have h1 : G.Reachable 0 1 := SimpleGraph.Adj.reachable (by decide)
  intro v
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact h1
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact h1.trans (SimpleGraph.Adj.reachable (by decide))
  · exact h1.trans (SimpleGraph.Adj.reachable (by decide))

theorem hacyc : G.IsAcyclic := by
  have ht : G.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨?_, ?_⟩
    · exact SimpleGraph.Connected.mk (fun u v => (hreach u).symm.trans (hreach v))
    · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcard]
      simp
  exact ht.isAcyclic

end PEqualNP.Outside.L_meta_758_aux

open PEqualNP.Outside.L_meta_758_aux in
theorem PEqualNP.Outside.L_meta_758 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s := by
  intro s
  rw [hf]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 2 s G hacyc hedge hcover h
    rw [hcard] at this
    omega
  · intro hs
    obtain ⟨C, h1, h2, h3⟩ := PEqualNP.MetaComplexity.L105 6 G {0, 1} hedge hT
    refine ⟨C, h1, ?_, h3⟩
    rw [hcard] at h2
    have : ({0, 1} : Finset (Fin 6)).card = 2 := by decide
    rw [this] at h2
    omega
