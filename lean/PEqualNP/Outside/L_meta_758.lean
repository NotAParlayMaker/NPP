import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_758

private def links758 (a b : Fin 6) : Prop :=
  (a = 0 ∧ (b = 1 ∨ b = 2 ∨ b = 3)) ∨ (a = 1 ∧ (b = 4 ∨ b = 5))

private def graph758 : SimpleGraph (Fin 6) where
  Adj a b := links758 a b ∨ links758 b a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by unfold links758; decide⟩

private abbrev decAdj758 : DecidableRel graph758.Adj := by
  intro i j
  change Decidable (links758 i j ∨ links758 j i)
  unfold links758
  infer_instance

theorem bound : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s := by
  intro s
  let _ : DecidableRel graph758.Adj := decAdj758
  have tree758 : graph758.IsTree := by
    apply SimpleGraph.isTree_iff_connected_and_card.mpr
    constructor
    · refine (graph758.connected_iff_exists_forall_reachable).mpr ⟨0, ?_⟩
      intro i
      fin_cases i
      · exact SimpleGraph.Reachable.refl _
      · exact SimpleGraph.Adj.reachable (show graph758.Adj 0 1 by decide)
      · exact SimpleGraph.Adj.reachable (show graph758.Adj 0 2 by decide)
      · exact SimpleGraph.Adj.reachable (show graph758.Adj 0 3 by decide)
      · exact (SimpleGraph.Adj.reachable (show graph758.Adj 0 1 by decide)).trans
          (SimpleGraph.Adj.reachable (show graph758.Adj 1 4 by decide))
      · exact (SimpleGraph.Adj.reachable (show graph758.Adj 0 1 by decide)).trans
          (SimpleGraph.Adj.reachable (show graph758.Adj 1 5 by decide))
    · simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide

  have function758 :
      (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) =
      (fun x : Fin 6 → Bool => decide (∃ i j, graph758.Adj i j ∧ x i = true ∧ x j = true)) := by
    funext x
    have h : ∀ y : Fin 6 → Bool,
        ((y 0 && y 1) || (y 0 && y 2) || (y 0 && y 3) || (y 1 && y 4) || (y 1 && y 5)) =
        decide (∃ i j, graph758.Adj i j ∧ y i = true ∧ y j = true) := by decide
    exact h x

  have edges758 : graph758.edgeFinset.card = 5 := by decide

  have cover758 : ∀ T : Finset (Fin 6),
      (∀ i j, graph758.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by decide
  rw [function758]
  have hasEdge : ∃ i j : Fin 6, graph758.Adj i j := ⟨0, 1, by decide⟩
  constructor
  · intro h
    have low := PEqualNP.MetaComplexity.L104 6 2 s graph758 tree758.isAcyclic
      hasEdge cover758 h
    rw [edges758] at low
    omega
  · intro hs
    let T : Finset (Fin 6) := {0, 1}
    have covers : ∀ i j, graph758.Adj i j → i ∈ T ∨ j ∈ T := by decide
    have cardT : T.card = 2 := by decide
    obtain ⟨C, fan, sz, comp⟩ := PEqualNP.MetaComplexity.L105 6 graph758 T hasEdge covers
    rw [edges758, cardT] at sz
    exact ⟨C, fan, by omega, comp⟩

end PEqualNP.Outside.L_meta_758

theorem PEqualNP.Outside.L_meta_758 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s :=
  PEqualNP.Outside.L_meta_758.bound
