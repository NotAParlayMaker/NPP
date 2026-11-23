import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_755_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Eedges : Finset (Sym2 (Fin 6)) := {s(0,1), s(0,2), s(0,3), s(4,5)}

def G : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet (Eedges : Set (Sym2 (Fin 6)))

private lemma G_adj (i j : Fin 6) :
    G.Adj i j ↔ (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨
      (i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
      (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
  fin_cases i <;> fin_cases j <;> simp [G, SimpleGraph.fromEdgeSet_adj, Eedges]

private lemma G_edgeSet : G.edgeSet = (Eedges : Set (Sym2 (Fin 6))) := by
  apply Set.ext
  intro e
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, G_adj a b]
    simp [Eedges]
    tauto

private lemma G_acyclic : G.IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  intro e he
  rw [G_edgeSet] at he
  simp [Eedges] at he
  rcases he with rfl | rfl | rfl | rfl
  · rw [SimpleGraph.isBridge_iff]
    apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty (huv := by decide)
    ext v
    simp [G, SimpleGraph.deleteEdges, SimpleGraph.fromEdgeSet_adj, Eedges]
  · rw [SimpleGraph.isBridge_iff]
    apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty (huv := by decide)
    ext v
    simp [G, SimpleGraph.deleteEdges, SimpleGraph.fromEdgeSet_adj, Eedges]
  · rw [SimpleGraph.isBridge_iff]
    apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty (huv := by decide)
    ext v
    simp [G, SimpleGraph.deleteEdges, SimpleGraph.fromEdgeSet_adj, Eedges]
  · rw [SimpleGraph.isBridge_iff]
    apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty (huv := by decide)
    ext v
    simp [G, SimpleGraph.deleteEdges, SimpleGraph.fromEdgeSet_adj, Eedges]

private lemma G_ncard : G.edgeSet.ncard = 4 := by
  rw [G_edgeSet]
  rw [Set.ncard_coe_finset]
  decide


def f : (Fin 6 → Bool) → Bool :=
  fun x => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)

private lemma G_cover (T : Finset (Fin 6))
    (hT : ∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) : 2 ≤ T.card := by
  have h01 : (0 : Fin 6) ∈ T ∨ (1 : Fin 6) ∈ T :=
    hT 0 1 ((G_adj 0 1).mpr (Or.inl ⟨rfl, rfl⟩))
  have h45 : (4 : Fin 6) ∈ T ∨ (5 : Fin 6) ∈ T :=
    hT 4 5 ((G_adj 4 5).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
  rcases h01 with h0 | h1 <;> rcases h45 with h4 | h5
  · have hsub : ({0, 4} : Finset (Fin 6)) ⊆ T := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    simpa using this
  · have hsub : ({0, 5} : Finset (Fin 6)) ⊆ T := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    simpa using this
  · have hsub : ({1, 4} : Finset (Fin 6)) ⊆ T := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    simpa using this
  · have hsub : ({1, 5} : Finset (Fin 6)) ⊆ T := by
      intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
    have := Finset.card_le_card hsub
    simpa using this

private lemma lower (G : SimpleGraph (Fin 6)) [DecidableRel G.Adj]
    (hacyc : G.IsAcyclic) (hedge : ∃ i j : Fin 6, G.Adj i j)
    (hfun : ∀ x : Fin 6 → Bool,
      decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true) = f x)
    (hcover : ∀ T : Finset (Fin 6), (∀ i j : Fin 6, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card)
    (hE : G.edgeSet.ncard = 4) :
    ∀ s : ℕ, HasCircuitSize 6 f s → 5 ≤ s := by
  intro s hs
  have hs' : HasCircuitSize 6
      (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) s := by
    rwa [show (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) = f from funext hfun]
  have h104 := PEqualNP.MetaComplexity.L104 6 2 s G hacyc hedge hcover hs'
  have hEf : G.edgeFinset.card = 4 := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, hE]
  rw [hEf] at h104
  omega

def C : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [1, 2] },
      { op := GateOp.or, inputs := [6, 3] },
      { op := GateOp.and, inputs := [0, 7] },
      { op := GateOp.and, inputs := [4, 5] },
      { op := GateOp.or, inputs := [8, 9] }],
    output := 10 }

private lemma C_fan : FanInTwo C := by simp [FanInTwo, C]
private lemma C_size : C.size = 5 := rfl
private lemma C_eval (x : Fin 6 → Bool) : C.eval (List.ofFn x) = f x := by
  simp [C, f, Circuit.eval, Circuit.wires, GateOp.eval, Bool.and_or_distrib_left]


end PEqualNP.Outside.L_meta_755_aux

open PEqualNP.Outside.L_meta_755_aux

theorem PEqualNP.Outside.L_meta_755 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 4 && x 5)) s ↔
      5 ≤ s := by
  change ∀ s, PEqualNP.MetaComplexity.HasCircuitSize 6 f s ↔ 5 ≤ s
  intro s
  constructor
  · intro hs
    haveI : DecidableRel G.Adj := by unfold G; infer_instance
    have hfun : ∀ x : Fin 6 → Bool,
        decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true) = f x := by
      intro x
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      constructor
      · rintro ⟨i, j, hij, hxi, hxj⟩
        rcases (G_adj i j).mp hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [f, hxi, hxj]
      · intro h
        simp [f, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with ((h | h) | h) | h
        · exact ⟨0, 1, (G_adj 0 1).mpr (Or.inl ⟨rfl, rfl⟩), h.1, h.2⟩
        · exact ⟨0, 2, (G_adj 0 2).mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), h.1, h.2⟩
        · exact ⟨0, 3, (G_adj 0 3).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))), h.1, h.2⟩
        · exact ⟨4, 5, (G_adj 4 5).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))), h.1, h.2⟩
    exact lower G G_acyclic ⟨0, 1, (G_adj 0 1).mpr (Or.inl ⟨rfl, rfl⟩)⟩ hfun
      (fun T hT => G_cover T hT) G_ncard s hs
  · intro hs
    exact ⟨C, C_fan, by rw [C_size]; exact hs, C_eval⟩
