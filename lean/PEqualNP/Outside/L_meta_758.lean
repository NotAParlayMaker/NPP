import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_758


abbrev graph : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (fun u v => (u, v) ∈ ([(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)] :
    List (Fin 6 × Fin 6)))

abbrev target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)

lemma function_eq : target = (fun x : Fin 6 → Bool =>
    decide (∃ i j : Fin 6, graph.Adj i j ∧ x i = true ∧ x j = true)) := by
  exact funext (by decide)

lemma five_edges : graph.edgeFinset.card = 5 := by decide

lemma forest : graph.IsAcyclic := by
  let adjDec (u v : Fin 6) : Decidable (graph.Adj u v) :=
    (inferInstance : DecidableRel graph.Adj) u v
  have paths : ∀ v : Fin 6, v = 0 ∨ graph.Adj 0 v ∨ (graph.Adj 0 1 ∧ graph.Adj 1 v) := by
    decide
  have from_zero (v : Fin 6) : graph.Reachable 0 v := by
    rcases paths v with rfl | h | ⟨h, h'⟩
    · exact SimpleGraph.Reachable.refl _
    · exact h.reachable
    · exact h.reachable.trans h'.reachable
  have conn : graph.Connected := ⟨fun u v => (from_zero u).symm.trans (from_zero v)⟩
  apply (SimpleGraph.isTree_iff_connected_and_card.mpr ⟨conn, ?_⟩).isAcyclic
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, five_edges,
    Nat.card_eq_fintype_card, Fintype.card_fin]

end PEqualNP.Outside.L_meta_758

open PEqualNP.Outside.L_meta_758

theorem PEqualNP.Outside.L_meta_758 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s := by
  intro s
  change PEqualNP.MetaComplexity.HasCircuitSize 6 target s ↔ _
  rw [function_eq]
  have edge : ∃ i j : Fin 6, graph.Adj i j := by decide
  constructor
  · intro circ
    have cover : ∀ T : Finset (Fin 6),
        (∀ i j : Fin 6, graph.Adj i j → i ∈ T ∨ j ∈ T) →
          2 ≤ T.card := by decide
    have h := PEqualNP.MetaComplexity.L104 6 2 s _ forest edge cover circ
    rw [five_edges] at h
    omega
  · intro hs
    let centers : Finset (Fin 6) := {0, 1}
    have cover : ∀ i j : Fin 6, graph.Adj i j →
        i ∈ centers ∨ j ∈ centers := by decide
    obtain ⟨C, hC, hsize, hfun⟩ := PEqualNP.MetaComplexity.L105 6 _ centers edge cover
    refine ⟨C, hC, hsize.trans ?_, hfun⟩
    rw [five_edges]
    exact hs
