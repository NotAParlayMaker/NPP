import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_756_aux

def adjB (i j : Fin 6) : Bool :=
  decide ((i.val, j.val) ∈ [(0,1),(1,0),(0,2),(2,0),(0,3),(3,0),(0,4),(4,0),(1,5),(5,1)])

def G : SimpleGraph (Fin 6) where
  Adj i j := adjB i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance instDecAdj : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (adjB i j = true))

theorem hcard : G.edgeFinset.card = 5 := by decide

theorem hcover : ∀ i j : Fin 6, G.Adj i j → i ∈ ({0, 1} : Finset (Fin 6)) ∨ j ∈ ({0, 1} : Finset (Fin 6)) := by
  decide

theorem hmin : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T hT
  have e01 := hT 0 1 (by decide)
  have e02 := hT 0 2 (by decide)
  have e03 := hT 0 3 (by decide)
  have e15 := hT 1 5 (by decide)
  have : 1 < T.card := by
    rw [Finset.one_lt_card]
    by_cases h0 : (0 : Fin 6) ∈ T
    · rcases e15 with h | h
      · exact ⟨0, h0, 1, h, by decide⟩
      · exact ⟨0, h0, 5, h, by decide⟩
    · have h2 : (2 : Fin 6) ∈ T := e02.resolve_left h0
      have h3 : (3 : Fin 6) ∈ T := e03.resolve_left h0
      exact ⟨2, h2, 3, h3, by decide⟩
  omega

theorem hconn : G.Connected := by
  have h : ∀ v : Fin 6, G.Reachable 0 v := by
    intro v
    have a01 : G.Adj 0 1 := by decide
    have a02 : G.Adj 0 2 := by decide
    have a03 : G.Adj 0 3 := by decide
    have a04 : G.Adj 0 4 := by decide
    have a15 : G.Adj 1 5 := by decide
    fin_cases v
    · exact SimpleGraph.Reachable.refl _
    · exact a01.reachable
    · exact a02.reachable
    · exact a03.reachable
    · exact a04.reachable
    · exact a01.reachable.trans a15.reachable
  exact ⟨fun u v => (h u).symm.trans (h v)⟩

theorem hacyc : G.IsAcyclic := by
  have ht : G.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨hconn, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hcard]
    simp
  exact ht.isAcyclic

theorem hf : (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5))
    = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  revert x
  decide

end PEqualNP.Outside.L_meta_756_aux

open PEqualNP.Outside.L_meta_756_aux in
theorem PEqualNP.Outside.L_meta_756 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s := by
  intro s
  rw [hf]
  constructor
  · intro h
    have := PEqualNP.MetaComplexity.L104 6 2 s G hacyc ⟨0, 1, by decide⟩ hmin h
    rw [hcard] at this
    omega
  · intro h
    obtain ⟨C, h1, h2, h3⟩ := PEqualNP.MetaComplexity.L105 6 G {0, 1} ⟨0, 1, by decide⟩ hcover
    rw [hcard] at h2
    exact ⟨C, h1, by simp at h2; omega, h3⟩
