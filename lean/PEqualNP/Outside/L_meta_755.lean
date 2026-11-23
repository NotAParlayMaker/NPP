import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755

open SimpleGraph PEqualNP.MetaComplexity
open scoped Sym2

private abbrev emptyGraph : SimpleGraph (Fin 6) := ⊥
private abbrev firstEdge := emptyGraph ⊔ SimpleGraph.edge 0 1
private abbrev twoEdges := firstEdge ⊔ SimpleGraph.edge 0 2
private abbrev threeEdges := twoEdges ⊔ SimpleGraph.edge 0 3
private abbrev forest := threeEdges ⊔ SimpleGraph.edge 4 5

private abbrev oriented (a b : Fin 6) : Prop :=
  (a = 0 ∧ (b = 1 ∨ b = 2 ∨ b = 3)) ∨ (a = 4 ∧ b = 5)

set_option maxHeartbeats 1000000 in
private lemma forestAdj (a b : Fin 6) :
    forest.Adj a b ↔ oriented a b ∨ oriented b a := by
  fin_cases a <;> fin_cases b <;>
    simp [forest, threeEdges, twoEdges, firstEdge, emptyGraph,
      SimpleGraph.sup_adj, SimpleGraph.edge_adj, oriented]

private abbrev forestDecision : DecidableRel forest.Adj := fun a b =>
  decidable_of_iff (oriented a b ∨ oriented b a) (forestAdj a b).symm

private lemma edgesCard (f : Fintype forest.edgeSet) :
    (@SimpleGraph.edgeFinset (Fin 6) forest f).card = 4 := by
  have h : @SimpleGraph.edgeFinset (Fin 6) forest f =
      {s((0 : Fin 6),1), s(0,2), s(0,3), s(4,5)} := by
    ext e
    obtain ⟨a,b⟩ := e
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, forestAdj, oriented,
      Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    tauto
  rw [h]
  decide

private lemma separate (G : SimpleGraph (Fin 6)) (a b : Fin 6)
    (hne : a ≠ b) (hb : ∀ w, ¬ G.Adj b w) : ¬ G.Reachable a b := by
  apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hne
  ext w
  simp [SimpleGraph.mem_neighborSet, hb w]

private lemma acyclic : forest.IsAcyclic := by
  have h₁ : firstEdge.IsAcyclic :=
    SimpleGraph.isAcyclic_bot.sup_edge_of_not_reachable
      (separate emptyGraph 0 1 (by decide) (by simp [emptyGraph]))
  have h₂ : twoEdges.IsAcyclic :=
    h₁.sup_edge_of_not_reachable (separate firstEdge 0 2 (by decide) (by
      intro w
      simp [firstEdge, emptyGraph, SimpleGraph.edge_adj]))
  have h₃ : threeEdges.IsAcyclic :=
    h₂.sup_edge_of_not_reachable (separate twoEdges 0 3 (by decide) (by
      intro w
      simp [twoEdges, firstEdge, emptyGraph, SimpleGraph.sup_adj, SimpleGraph.edge_adj]))
  exact h₃.sup_edge_of_not_reachable (separate threeEdges 4 5 (by decide) (by
    intro w
    simp [threeEdges, twoEdges, firstEdge, emptyGraph, SimpleGraph.sup_adj, SimpleGraph.edge_adj]))

private lemma coverLower (T : Finset (Fin 6))
    (ht : ∀ i j : Fin 6, forest.Adj i j → i ∈ T ∨ j ∈ T) : 2 ≤ T.card := by
  let _ : DecidableRel forest.Adj := forestDecision
  have h01 : ∃ p ∈ T, p = 0 ∨ p = 1 := by
    rcases ht 0 1 (by decide) with h | h
    · exact ⟨0,h,Or.inl rfl⟩
    · exact ⟨1,h,Or.inr rfl⟩
  have h45 : ∃ q ∈ T, q = 4 ∨ q = 5 := by
    rcases ht 4 5 (by decide) with h | h
    · exact ⟨4,h,Or.inl rfl⟩
    · exact ⟨5,h,Or.inr rfl⟩
  obtain ⟨p,hp,hp'⟩ := h01
  obtain ⟨q,hq,hq'⟩ := h45
  have hne : p ≠ q := by
    rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;> decide
  rw [← Finset.card_pair hne]
  exact Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hp, Finset.singleton_subset_iff.mpr hq⟩)

private abbrev graphFunction (x : Fin 6 → Bool) : Bool :=
  letI : DecidableRel forest.Adj := forestDecision
  decide (∃ a b : Fin 6, forest.Adj a b ∧ x a = true ∧ x b = true)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
private lemma edgeFunction :
    graphFunction = (fun x : Fin 6 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) := by
  have pointwise : ∀ x : Fin 6 → Bool,
      graphFunction x = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) := by
    decide +kernel
  exact funext pointwise

theorem sizeIff (s : ℕ) : HasCircuitSize 6 graphFunction s ↔ 5 ≤ s := by
  let _ : DecidableRel forest.Adj := forestDecision
  have hEdge : ∃ i j : Fin 6, forest.Adj i j := ⟨0,1,by decide⟩
  constructor
  · intro hs
    have h := @L104 6 2 s forest forestDecision acyclic hEdge coverLower hs
    simp only [edgesCard] at h
    omega
  · intro hs
    let T : Finset (Fin 6) := {0,4}
    have hcover : ∀ i j : Fin 6, forest.Adj i j → i ∈ T ∨ j ∈ T := by decide
    obtain ⟨C,hmono,hsize,hfun⟩ := @L105 6 forest forestDecision T hEdge hcover
    simp only [edgesCard, show T.card = 2 by decide] at hsize
    exact ⟨C,hmono,hsize.trans hs,hfun⟩

end PEqualNP.Outside.L_meta_755

theorem PEqualNP.Outside.L_meta_755 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool =>
        (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔ 5 ≤ s := by
  intro s
  rw [← PEqualNP.Outside.L_meta_755.edgeFunction]
  exact PEqualNP.Outside.L_meta_755.sizeIff s
