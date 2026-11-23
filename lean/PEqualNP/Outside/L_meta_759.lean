import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_759_aux

open PEqualNP.MetaComplexity

private def endpoints : List (Fin 6 × Fin 6) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (4, 5)]

private def graph : SimpleGraph (Fin 6) where
  Adj i j := (i, j) ∈ endpoints ∨ (j, i) ∈ endpoints
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun i => by
    fin_cases i <;> decide⟩

private abbrev graphDec : DecidableRel graph.Adj :=
  fun i j => inferInstanceAs (Decidable ((i, j) ∈ endpoints ∨ (j, i) ∈ endpoints))

private def edgeCount : ℕ := by
  let _ : DecidableRel graph.Adj := graphDec
  exact graph.edgeFinset.card

private lemma edgeCount_eq : edgeCount = 5 := by decide

private lemma graph_has_edge : ∃ i j : Fin 6, graph.Adj i j :=
  ⟨0, 1, by
    let _ : DecidableRel graph.Adj := graphDec
    decide⟩

private lemma graph_acyclic : graph.IsAcyclic := by
  let _ : DecidableRel graph.Adj := graphDec
  have h01 : graph.Reachable 0 1 := (show graph.Adj 0 1 by decide).reachable
  have h14 : graph.Reachable 1 4 := (show graph.Adj 1 4 by decide).reachable
  have h45 : graph.Reachable 4 5 := (show graph.Adj 4 5 by decide).reachable
  have hreach (i : Fin 6) : graph.Reachable 0 i := by
    fin_cases i
    · exact SimpleGraph.Reachable.rfl
    · exact h01
    · exact (show graph.Adj 0 2 by decide).reachable
    · exact (show graph.Adj 0 3 by decide).reachable
    · exact h01.trans h14
    · exact h01.trans (h14.trans h45)
  have hconn : graph.Connected :=
    (SimpleGraph.connected_iff graph).mpr ⟨fun u v => (hreach u).symm.trans (hreach v), ⟨0⟩⟩
  refine (SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hconn, ?_⟩).isAcyclic
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  change edgeCount + 1 = 6
  simp [edgeCount_eq]

private def cover : Finset (Fin 6) := {0, 4}

private lemma cover_all : ∀ i j : Fin 6, graph.Adj i j → i ∈ cover ∨ j ∈ cover := by
  let _ : DecidableRel graph.Adj := graphDec
  decide

set_option maxHeartbeats 1000000 in
private lemma cover_lower :
    ∀ T : Finset (Fin 6), (∀ i j : Fin 6, graph.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by
  let _ : DecidableRel graph.Adj := graphDec
  decide

private def wanted (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)

set_option maxHeartbeats 1000000 in
private lemma wanted_eq :
    let _ : DecidableRel graph.Adj := graphDec
    wanted = (fun x : Fin 6 → Bool => decide (∃ i j : Fin 6, graph.Adj i j ∧ x i = true ∧ x j = true)) := by
  let _ : DecidableRel graph.Adj := graphDec
  funext x
  exact (show ∀ x : Fin 6 → Bool, wanted x =
    decide (∃ i j : Fin 6, graph.Adj i j ∧ x i = true ∧ x j = true) by decide) x

theorem mainProof (s : ℕ) : HasCircuitSize 6 wanted s ↔ 6 ≤ s := by
  let _ : DecidableRel graph.Adj := graphDec
  rw [wanted_eq]
  constructor
  · intro h
    have hl := L104 6 2 s graph graph_acyclic graph_has_edge cover_lower h
    change edgeCount + 2 ≤ s + 1 at hl
    rw [edgeCount_eq] at hl
    omega
  · intro hs
    have hu := L105 6 graph cover graph_has_edge cover_all
    have hsize : graph.edgeFinset.card + cover.card - 1 = 6 := by
      change edgeCount + cover.card - 1 = 6
      decide
    rw [hsize] at hu
    obtain ⟨C, hC, hsizeC, heval⟩ := hu
    exact ⟨C, hC, hsizeC.trans hs, heval⟩

end PEqualNP.Outside.L_meta_759_aux

theorem PEqualNP.Outside.L_meta_759 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 4 && x 5)) s ↔ 6 ≤ s :=
  PEqualNP.Outside.L_meta_759_aux.mainProof

