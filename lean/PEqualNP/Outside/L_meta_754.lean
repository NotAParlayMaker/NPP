import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_754

private abbrev edges : Finset (Sym2 (Fin 5)) := {s(0, 1), s(0, 2), s(0, 3), s(1, 4)}

private abbrev graph : SimpleGraph (Fin 5) := SimpleGraph.fromEdgeSet (↑edges)

private lemma edgeCount (finiteEdges : Fintype graph.edgeSet) :
    (@SimpleGraph.edgeFinset _ graph finiteEdges).card = 4 := by
  have edgeFinset_eq : @SimpleGraph.edgeFinset _ graph finiteEdges = edges := by
    apply Finset.coe_injective
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left]
    simp only [edges, Set.disjoint_left, Finset.mem_coe, Finset.mem_insert,
      Finset.mem_singleton, Sym2.mem_diagSet]
    intro e he
    rcases he with rfl | rfl | rfl | rfl <;> decide
  rw [edgeFinset_eq]
  decide

private lemma acyclic : graph.IsAcyclic := by
  have connected : graph.Connected := by
    refine graph.connected_iff_exists_forall_reachable.mpr ⟨0, ?_⟩
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.rfl
    · exact (show graph.Adj 0 1 by decide).reachable
    · exact (show graph.Adj 0 2 by decide).reachable
    · exact (show graph.Adj 0 3 by decide).reachable
    · exact (show graph.Adj 0 1 by decide).reachable.trans
        (show graph.Adj 1 4 by decide).reachable
  have tree : graph.IsTree := by
    refine SimpleGraph.isTree_iff_connected_and_card.mpr ⟨connected, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, edgeCount,
      Nat.card_eq_fintype_card]
    decide
  exact tree.isAcyclic

private lemma nonemptyEdges : ∃ i j : Fin 5, graph.Adj i j := ⟨0, 1, by decide⟩

private abbrev cover : Finset (Fin 5) := {0, 1}

private lemma isCover : ∀ i j : Fin 5, graph.Adj i j → i ∈ cover ∨ j ∈ cover := by decide

private lemma coverLower (T : Finset (Fin 5))
    (hT : ∀ i j : Fin 5, graph.Adj i j → i ∈ T ∨ j ∈ T) : 2 ≤ T.card := by
  apply Finset.one_lt_card.mpr
  rcases hT 0 2 (by decide) with h0 | h2 <;> rcases hT 1 4 (by decide) with h1 | h4
  · exact ⟨0, h0, 1, h1, by decide⟩
  · exact ⟨0, h0, 4, h4, by decide⟩
  · exact ⟨2, h2, 1, h1, by decide⟩
  · exact ⟨2, h2, 4, h4, by decide⟩

private lemma edgeFunction_eq :
    (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) =
      (fun x : Fin 5 → Bool => decide (∃ i j : Fin 5, graph.Adj i j ∧ x i = true ∧ x j = true)) := by
  apply funext
  decide

end PEqualNP.Outside.L_meta_754

theorem PEqualNP.Outside.L_meta_754 : ∀ s : ℕ,
    PEqualNP.MetaComplexity.HasCircuitSize 5
      (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔
    5 ≤ s := by
  intro s
  rw [L_meta_754.edgeFunction_eq]
  constructor
  · intro h
    have bound := PEqualNP.MetaComplexity.L104 5 2 s L_meta_754.graph L_meta_754.acyclic
      L_meta_754.nonemptyEdges L_meta_754.coverLower h
    rw [L_meta_754.edgeCount] at bound
    omega
  · intro hs
    have upper := PEqualNP.MetaComplexity.L105 5 L_meta_754.graph L_meta_754.cover
      L_meta_754.nonemptyEdges L_meta_754.isCover
    rw [L_meta_754.edgeCount] at upper
    have hcover : L_meta_754.cover.card = 2 := by decide
    rw [hcover] at upper
    obtain ⟨C, hC, hsize, heval⟩ := upper
    exact ⟨C, hC, hsize.trans hs, heval⟩
