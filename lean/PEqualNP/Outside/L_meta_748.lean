import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_748

private def links748 (a b : Fin 6) : Prop :=
  a = 0 ∧ b ≠ 0

private def graph748 : SimpleGraph (Fin 6) where
  Adj a b := links748 a b ∨ links748 b a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by unfold links748; decide⟩

private abbrev decAdj748 : DecidableRel graph748.Adj := by
  intro i j
  change Decidable (links748 i j ∨ links748 j i)
  unfold links748
  infer_instance

theorem bound : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) s ↔ 5 ≤ s := by
  intro s
  let _ : DecidableRel graph748.Adj := decAdj748
  have tree748 : graph748.IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    constructor
    · refine (graph748.connected_iff_exists_forall_reachable).mpr ⟨0, ?_⟩
      intro i
      by_cases h : i = 0
      · subst i
        exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (show graph748.Adj 0 i from Or.inl ⟨rfl, h⟩)
    · simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide

  have function748 :
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) =
      (fun x : Fin 6 → Bool => decide (∃ i j, graph748.Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x
    have h : ∀ y : Fin 6 → Bool,
        ((y 0 && y 1) || (y 0 && y 2) || (y 0 && y 3) || (y 0 && y 4) || (y 0 && y 5)) =
        decide (∃ i j, graph748.Adj i j ∧ y i = true ∧ y j = true) := by decide
    exact h x

  have edges748 : graph748.edgeFinset.card = 5 := by decide

  have cover748 : ∀ T : Finset (Fin 6),
      (∀ i j, graph748.Adj i j → i ∈ T ∨ j ∈ T) → 1 ≤ T.card := by decide
  rw [function748]
  have hasEdge : ∃ i j : Fin 6, graph748.Adj i j := ⟨0, 1, by decide⟩
  constructor
  · intro h
    have low := PEqualNP.MetaComplexity.L104 6 1 s graph748 tree748.isAcyclic
      hasEdge cover748 h
    rw [edges748] at low
    omega
  · intro hs
    let T : Finset (Fin 6) := {0}
    have covers : ∀ i j, graph748.Adj i j → i ∈ T ∨ j ∈ T := by decide
    have cardT : T.card = 1 := by decide
    obtain ⟨C, fan, sz, comp⟩ := PEqualNP.MetaComplexity.L105 6 graph748 T hasEdge covers
    rw [edges748, cardT] at sz
    exact ⟨C, fan, by omega, comp⟩

end PEqualNP.Outside.L_meta_748

theorem PEqualNP.Outside.L_meta_748 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5)) s ↔ 5 ≤ s :=
  PEqualNP.Outside.L_meta_748.bound
