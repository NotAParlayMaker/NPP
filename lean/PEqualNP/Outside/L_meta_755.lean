import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755

open SimpleGraph
open PEqualNP.MetaComplexity

-- The graph of the statement: a star with three leaves at vertex 0 and a disjoint edge 4-5.
abbrev G : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun i j =>
  (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨ (i = 4 ∧ j = 5))

-- A tree on the same vertex set that contains G: add the edge 0-4.
abbrev H : SimpleGraph (Fin 6) := SimpleGraph.fromRel (fun i j =>
  (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4)) ∨ (i = 4 ∧ j = 5))

abbrev ef := fun x : Fin 6 → Bool =>
  decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)

theorem firstEdge : G.Adj 0 1 := by decide

theorem subGraph : G ≤ H := by
  intro i j hij
  rw [SimpleGraph.fromRel_adj] at hij ⊢
  refine ⟨hij.1, ?_⟩
  rcases hij.2 with h | h
  · left
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · left
      exact ⟨hi, by rcases hj with rfl | rfl | rfl <;> simp⟩
    · right
      exact ⟨hi, hj⟩
  · right
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · left
      exact ⟨hi, by rcases hj with rfl | rfl | rfl <;> simp⟩
    · right
      exact ⟨hi, hj⟩

theorem connectedH : H.Connected := by
  have r : ∀ i : Fin 6, H.Reachable 0 i := by
    intro i
    fin_cases i
    · exact SimpleGraph.Reachable.refl _
    · exact (show H.Adj 0 1 by decide).reachable
    · exact (show H.Adj 0 2 by decide).reachable
    · exact (show H.Adj 0 3 by decide).reachable
    · exact (show H.Adj 0 4 by decide).reachable
    · exact (show H.Adj 0 4 by decide).reachable.trans (show H.Adj 4 5 by decide).reachable
  exact ⟨fun a b => (r a).symm.trans (r b)⟩

set_option maxRecDepth 10000 in
theorem edgesH : H.edgeFinset.card = 5 := by decide

theorem acyclicH : H.IsAcyclic := by
  apply SimpleGraph.IsTree.isAcyclic
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connectedH, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, edgesH, Nat.card_fin]

theorem forestG : G.IsAcyclic := SimpleGraph.IsAcyclic.anti subGraph acyclicH

set_option maxRecDepth 10000 in
theorem edgesG : G.edgeFinset.card = 4 := by decide

abbrev T : Finset (Fin 6) := {0, 4}

theorem coverG : ∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T := by decide

set_option maxRecDepth 20000 in
theorem lowerCover : ∀ S : Finset (Fin 6),
    (∀ i j : Fin 6, G.Adj i j → i ∈ S ∨ j ∈ S) → 2 ≤ S.card := by decide

set_option maxRecDepth 20000 in
theorem evalG : ∀ x : Fin 6 → Bool,
    ef x = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) := by decide

end PEqualNP.Outside.L_meta_755

open PEqualNP.Outside.L_meta_755

theorem PEqualNP.Outside.L_meta_755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [← funext evalG]
  constructor
  · intro h
    have hb := PEqualNP.MetaComplexity.L104 6 2 s G forestG ⟨0, 1, firstEdge⟩ lowerCover h
    rw [edgesG] at hb
    omega
  · intro hs
    have hu := PEqualNP.MetaComplexity.L105 6 G T ⟨0, 1, firstEdge⟩ coverG
    have ct : T.card = 2 := by decide
    rw [edgesG, ct] at hu
    obtain ⟨C, ho, hl, he⟩ := hu
    exact ⟨C, ho, le_trans hl hs, he⟩
