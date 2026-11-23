import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

namespace PEqualNP.Outside.L_meta_758

open PEqualNP.MetaComplexity SimpleGraph

abbrev G : SimpleGraph (Fin 6) := SimpleGraph.fromRel
  (fun i j => (i,j) ∈ ([(0,1),(0,2),(0,3),(1,4),(1,5)] : List (Fin 6 × Fin 6)))

lemma edge_count : G.edgeFinset.card = 5 := by decide

lemma tree : G.IsTree := by
  have h01 : G.Adj 0 1 := by decide
  have root (i : Fin 6) : G.Reachable 0 i := by
    fin_cases i
    · exact .refl _
    · exact h01.reachable
    · exact (show G.Adj 0 2 by decide).reachable
    · exact (show G.Adj 0 3 by decide).reachable
    · exact h01.reachable.trans (show G.Adj 1 4 by decide).reachable
    · exact h01.reachable.trans (show G.Adj 1 5 by decide).reachable
  apply (SimpleGraph.isTree_iff_connected_and_card).mpr
  refine ⟨⟨fun i j => (root i).symm.trans (root j)⟩, ?_⟩
  rw [Nat.card_eq_fintype_card, ← G.edgeFinset_card, edge_count]
  simp

abbrev f (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)

lemma fn_eq : f = (fun x : Fin 6 → Bool =>
    decide (∃ i j : Fin 6, G.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  revert x
  decide

end PEqualNP.Outside.L_meta_758

open PEqualNP.Outside.L_meta_758 PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_758 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)) s ↔ 6 ≤ s := by
  intro s
  change HasCircuitSize 6 f s ↔ 6 ≤ s
  rw [fn_eq]
  have edge : ∃ i j, G.Adj i j := ⟨0,1, by decide⟩
  constructor
  · intro h
    have cover : ∀ T : Finset (Fin 6), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) → 2 ≤ T.card := by decide
    have bound := L104 6 2 s G tree.isAcyclic edge cover h
    rw [edge_count] at bound
    omega
  · intro hs
    have cover : ∀ i j, G.Adj i j → i ∈ ({0,1} : Finset (Fin 6)) ∨ j ∈ ({0,1} : Finset (Fin 6)) := by decide
    obtain ⟨C,ok,size,correct⟩ := L105 6 G {0,1} edge cover
    rw [edge_count] at size
    exact ⟨C,ok,size.trans (by simpa using hs),correct⟩
