import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.LMeta758

open PEqualNP.MetaComplexity

abbrev dsRel (u v : Fin 6) : Prop :=
  (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 2) ∨ (u = 0 ∧ v = 3) ∨
    (u = 1 ∧ v = 4) ∨ (u = 1 ∧ v = 5)

abbrev dsGraph : SimpleGraph (Fin 6) := SimpleGraph.fromRel dsRel

def dsGraphByEdges : SimpleGraph (Fin 6) :=
  (((((⊥ : SimpleGraph (Fin 6)) ⊔ SimpleGraph.edge 0 1) ⊔ SimpleGraph.edge 0 2) ⊔
    SimpleGraph.edge 0 3) ⊔ SimpleGraph.edge 1 4) ⊔ SimpleGraph.edge 1 5

set_option maxRecDepth 10000 in
lemma dsGraph_eq_byEdges : dsGraph = dsGraphByEdges := by
  ext u v
  simp only [dsGraph, dsGraphByEdges, dsRel, SimpleGraph.fromRel_adj,
    SimpleGraph.sup_adj, SimpleGraph.bot_adj, SimpleGraph.edge_adj, false_or]
  aesop

lemma acyclic_add_edge {G : SimpleGraph (Fin 6)} {u v : Fin 6}
    (hG : G.IsAcyclic) (huv : u ≠ v) (hv : ∀ w, ¬ G.Adj v w) :
    (G ⊔ SimpleGraph.edge u v).IsAcyclic := by
  apply hG.sup_edge_of_not_reachable
  apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty huv
  ext w
  simp [SimpleGraph.mem_neighborSet, hv w]

lemma dsGraph_acyclic : dsGraph.IsAcyclic := by
  rw [dsGraph_eq_byEdges]
  unfold dsGraphByEdges
  refine acyclic_add_edge ?_ (by decide) (by intro w; simp [SimpleGraph.edge_adj])
  refine acyclic_add_edge ?_ (by decide) (by intro w; simp [SimpleGraph.edge_adj])
  refine acyclic_add_edge ?_ (by decide) (by intro w; simp [SimpleGraph.edge_adj])
  refine acyclic_add_edge ?_ (by decide) (by intro w; simp [SimpleGraph.edge_adj])
  refine acyclic_add_edge ?_ (by decide) (by intro w; simp)
  exact SimpleGraph.isAcyclic_bot

lemma dsGraph_has_edge : ∃ i j : Fin 6, dsGraph.Adj i j := by
  exact ⟨0, 1, by decide⟩

lemma dsGraph_edges : dsGraph.edgeFinset.card = 5 := by
  decide +kernel

lemma dsGraph_cover : ∀ i j : Fin 6, dsGraph.Adj i j →
    i ∈ ({0, 1} : Finset (Fin 6)) ∨ j ∈ ({0, 1} : Finset (Fin 6)) := by
  decide +kernel

lemma dsGraph_cover_min : ∀ T : Finset (Fin 6),
    (∀ i j : Fin 6, dsGraph.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  intro T h
  by_cases h0 : 0 ∈ T
  · by_cases h1 : 1 ∈ T
    · exact Finset.one_lt_card.mpr ⟨0, h0, 1, h1, by decide⟩
    · have h4 : 4 ∈ T := (h 1 4 (by decide)).resolve_left h1
      exact Finset.one_lt_card.mpr ⟨0, h0, 4, h4, by decide⟩
  · have h2 : 2 ∈ T := (h 0 2 (by decide)).resolve_left h0
    have h3 : 3 ∈ T := (h 0 3 (by decide)).resolve_left h0
    exact Finset.one_lt_card.mpr ⟨2, h2, 3, h3, by decide⟩

lemma dsFun_eq : (fun x : Fin 6 → Bool =>
    (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) =
    (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6,
      dsGraph.Adj i j ∧ x i = true ∧ x j = true)) := by
  have h : ∀ x : Fin 6 → Bool,
      ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) =
        decide (∃ i j : Fin 6, dsGraph.Adj i j ∧ x i = true ∧ x j = true) := by
    decide +kernel
  exact funext h

lemma hasCircuitSize_mono' {n s t : ℕ} {f : (Fin n → Bool) → Bool}
    (h : HasCircuitSize n f s) (hst : s ≤ t) : HasCircuitSize n f t := by
  obtain ⟨C, hC, hsize, heval⟩ := h
  exact ⟨C, hC, hsize.trans hst, heval⟩

end PEqualNP.Outside.LMeta758

theorem PEqualNP.Outside.L_meta_758 : ∀ s : ℕ,
    PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s := by
  intro s
  rw [PEqualNP.Outside.LMeta758.dsFun_eq]
  constructor
  · intro hs
    have h := PEqualNP.MetaComplexity.L104 6 2 s PEqualNP.Outside.LMeta758.dsGraph
      PEqualNP.Outside.LMeta758.dsGraph_acyclic
      PEqualNP.Outside.LMeta758.dsGraph_has_edge
      PEqualNP.Outside.LMeta758.dsGraph_cover_min hs
    rw [PEqualNP.Outside.LMeta758.dsGraph_edges] at h
    omega
  · intro hs
    have h := PEqualNP.MetaComplexity.L105 6 PEqualNP.Outside.LMeta758.dsGraph
      {0, 1} PEqualNP.Outside.LMeta758.dsGraph_has_edge
      PEqualNP.Outside.LMeta758.dsGraph_cover
    norm_num [PEqualNP.Outside.LMeta758.dsGraph_edges] at h
    exact PEqualNP.Outside.LMeta758.hasCircuitSize_mono' h hs
