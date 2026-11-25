import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17665

private def pairs : List (ℕ × ℕ) := [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

private def graph := PEqualNP.EdgeOwnership.edgeGraph 11 pairs

private def key (e : ℕ × ℕ) : Sym2 (Fin 11) :=
  s(Fin.ofNat 11 e.1, Fin.ofNat 11 e.2)

private def keys := pairs.map key

private theorem keys_nodup : keys.Nodup := by decide +kernel

private theorem adjacency : ∀ a b : Fin 11, graph.Adj a b ↔ s(a,b) ∈ keys := by
  unfold graph
  decide +kernel

private theorem listed_edge : ∀ e ∈ pairs,
    graph.Adj (Fin.ofNat 11 e.1) (Fin.ofNat 11 e.2) := by
  unfold graph
  decide +kernel

private def uncovered (S : Finset (Fin 11)) : List (ℕ × ℕ) :=
  pairs.filter fun e => decide (Fin.ofNat 11 e.1 ∉ S ∧ Fin.ofNat 11 e.2 ∉ S)

private def minUncovered : List ℕ := [16,12,8,5,3,2,1,0,0,0,0,0]

private def allowance : List ℕ := [0,0,2,4,5,7,8,9,11,12,13,14,16,17,18,19,21]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem min_check : ∀ S : Finset (Fin 11),
    minUncovered.getD S.card 0 ≤ (uncovered S).length := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem numeric : ∀ (s : Fin 12) (k : Fin 17), minUncovered.getD s.val 0 ≤ k.val →
    5 + k.val ≤ s.val + allowance.getD k.val 0 := by decide +kernel

end PEqualNP.Outside.L_meta_17665

open PEqualNP.Outside.L_meta_17665

theorem PEqualNP.Outside.L_meta_17665 : (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj], x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → ∀ x4 ⊆ x1.edgeFinset, ∀ (x6 : Finset (Fin (11 : ℕ))), (x1.deleteEdges ↑x4).IsVertexCover ↑x6 → (5 : ℕ) + x4.card ≤ x6.card + [(0 : ℕ), (0 : ℕ), (2 : ℕ), (4 : ℕ), (5 : ℕ), (7 : ℕ), (8 : ℕ), (9 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (21 : ℕ)].getD x4.card (0 : ℕ)) := by
  intro G _ hG deleted hdeleted S hcover
  have hG' : G = graph := hG
  have hk : deleted.card < 17 := by
    have hsub : deleted ⊆ keys.toFinset := by
      intro e he
      have hedge := SimpleGraph.mem_edgeFinset.mp (hdeleted he)
      induction e using Sym2.inductionOn with
      | _ a b =>
        have ha : G.Adj a b := hedge
        rw [hG'] at ha
        exact List.mem_toFinset.mpr ((adjacency a b).mp ha)
    have h := Finset.card_le_card hsub
    have heq : keys.toFinset.card = 16 := by decide +kernel
    omega
  have hSub : ((uncovered S).map key).toFinset ⊆ deleted := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    have hs := List.mem_filter.mp hp
    have hm : Fin.ofNat 11 p.1 ∉ S ∧ Fin.ofNat 11 p.2 ∉ S := by
      simpa using hs.2
    by_contra hnot
    have hadj : G.Adj (Fin.ofNat 11 p.1) (Fin.ofNat 11 p.2) := by
      rw [hG']
      exact listed_edge p hs.1
    have hremain : (G.deleteEdges ↑deleted).Adj (Fin.ofNat 11 p.1) (Fin.ofNat 11 p.2) :=
      SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hnot⟩
    exact (hcover hremain).elim hm.1 hm.2
  have hnd : ((uncovered S).map key).Nodup :=
    List.Nodup.sublist (List.filter_sublist.map key) keys_nodup
  have hcard := Finset.card_le_card hSub
  rw [List.toFinset_card_of_nodup hnd, List.length_map] at hcard
  have hs : S.card < 12 := by
    have h := Finset.card_le_univ S
    simp at h
    omega
  exact numeric ⟨S.card, hs⟩ ⟨deleted.card, hk⟩ ((min_check S).trans hcard)
