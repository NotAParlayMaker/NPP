import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_756

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

def edges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (1, 5)]

def rel (u v : Fin 6) : Bool :=
  decide ((u.val, v.val) ∈ edges ∨ (v.val, u.val) ∈ edges)

def graph : SimpleGraph (Fin 6) where
  Adj u v := rel u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun u v =>
  inferInstanceAs (Decidable (rel u v = true))

def f (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5)

def edgeFn (x : Fin 6 → Bool) : Bool :=
  decide (∃ i j : Fin 6, graph.Adj i j ∧ x i = true ∧ x j = true)

theorem hasEdge : ∃ i j : Fin 6, graph.Adj i j := ⟨0, 1, by decide⟩

theorem cover_ok : ∀ i j : Fin 6, graph.Adj i j →
    i ∈ ({0, 1} : Finset (Fin 6)) ∨ j ∈ ({0, 1} : Finset (Fin 6)) := by
  decide

theorem tau_le : ∀ T : Finset (Fin 6),
    (∀ i j : Fin 6, graph.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  decide

theorem formula_eq (x : Fin 6 → Bool) : f x = edgeFn x := by
  revert x
  decide

theorem size_mono {g : (Fin 6 → Bool) → Bool} {s t : ℕ}
    (h : HasCircuitSize 6 g s) (hst : s ≤ t) : HasCircuitSize 6 g t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, le_trans h2 hst, h3⟩

theorem transport_to_edge {s : ℕ} (h : HasCircuitSize 6 f s) :
    HasCircuitSize 6 edgeFn s := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, h2, fun x => (formula_eq x) ▸ h3 x⟩

theorem transport_from_edge {s : ℕ} (h : HasCircuitSize 6 edgeFn s) :
    HasCircuitSize 6 f s := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1, h2, fun x => (formula_eq x).symm ▸ h3 x⟩

def fiveEdges : Finset (Sym2 (Fin 6)) :=
  {s((0 : Fin 6), 1), s(0, 2), s(0, 3), s(0, 4), s(1, 5)}

theorem fiveEdges_card : fiveEdges.card = 5 := by decide

theorem mem_edgeFinset_of_adj {a b : Fin 6} (h : graph.Adj a b) :
    s(a, b) ∈ graph.edgeFinset :=
  (SimpleGraph.mem_edgeFinset).mpr ((SimpleGraph.mem_edgeSet (G := graph)).mpr h)

theorem fiveEdges_subset : fiveEdges ⊆ graph.edgeFinset := by
  intro e he
  simp only [fiveEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact mem_edgeFinset_of_adj (by decide : graph.Adj 0 1)
  · exact mem_edgeFinset_of_adj (by decide : graph.Adj 0 2)
  · exact mem_edgeFinset_of_adj (by decide : graph.Adj 0 3)
  · exact mem_edgeFinset_of_adj (by decide : graph.Adj 0 4)
  · exact mem_edgeFinset_of_adj (by decide : graph.Adj 1 5)

theorem adj_mem_five (a b : Fin 6) (h : rel a b = true) : s(a, b) ∈ fiveEdges := by
  revert a b h
  decide

theorem edgeFinset_subset_five : graph.edgeFinset ⊆ fiveEdges := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    exact adj_mem_five a b
      ((SimpleGraph.mem_edgeSet (G := graph)).mp ((SimpleGraph.mem_edgeFinset).mp he))

theorem edgeFinset_card : graph.edgeFinset.card = 5 := by
  apply le_antisymm
  · exact (Finset.card_le_card edgeFinset_subset_five).trans_eq fiveEdges_card
  · exact fiveEdges_card.symm.trans_le (Finset.card_le_card fiveEdges_subset)

theorem reach_from_zero (v : Fin 6) : graph.Reachable 0 v := by
  fin_cases v
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by decide : graph.Adj 0 1)
  · exact SimpleGraph.Adj.reachable (by decide : graph.Adj 0 2)
  · exact SimpleGraph.Adj.reachable (by decide : graph.Adj 0 3)
  · exact SimpleGraph.Adj.reachable (by decide : graph.Adj 0 4)
  · exact (SimpleGraph.Adj.reachable (by decide : graph.Adj 0 1)).trans
      (SimpleGraph.Adj.reachable (by decide : graph.Adj 1 5))

theorem connected : graph.Connected where
  preconnected := fun u v => (reach_from_zero u).symm.trans (reach_from_zero v)
  nonempty := ⟨0⟩

theorem isTree : graph.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨connected, ?_⟩
  have hV : Nat.card (Fin 6) = 6 :=
    (Nat.card_eq_fintype_card).trans (Fintype.card_fin 6)
  have hE : Nat.card graph.edgeSet = 5 := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
    exact edgeFinset_card
  omega

theorem acyclic : graph.IsAcyclic := isTree.isAcyclic

theorem upper : HasCircuitSize 6 f 6 := by
  have h := L105 6 graph ({0, 1} : Finset (Fin 6)) hasEdge cover_ok
  have hs : graph.edgeFinset.card + ({0, 1} : Finset (Fin 6)).card - 1 = 6 := by
    rw [edgeFinset_card]
    decide
  rw [hs] at h
  exact transport_from_edge h

theorem lower {s : ℕ} (h : HasCircuitSize 6 f s) : 6 ≤ s := by
  have := L104 6 2 s graph acyclic hasEdge tau_le (transport_to_edge h)
  have := edgeFinset_card
  omega

theorem main (s : ℕ) : HasCircuitSize 6 f s ↔ 6 ≤ s :=
  ⟨lower, fun h6 => size_mono upper h6⟩

end PEqualNP.Outside.L_meta_756

theorem PEqualNP.Outside.L_meta_756 :
    ∀ s : ℕ,
      PEqualNP.MetaComplexity.HasCircuitSize 6
          (fun x : Fin 6 → Bool =>
            (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 5))
          s ↔
        6 ≤ s :=
  PEqualNP.Outside.L_meta_756.main
