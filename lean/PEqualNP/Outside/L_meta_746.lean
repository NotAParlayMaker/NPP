import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104

namespace PEqualNP.Outside.L_meta_746

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev St : SimpleGraph (Fin 4) where
  Adj i j := (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0)
  symm := ⟨fun i j h => by tauto⟩
  loopless := ⟨fun i h => by rcases h with h | h <;> exact h.2 h.1⟩

lemma st_conn : St.Connected := by
  have h0 : ∀ v : Fin 4, St.Reachable 0 v := by
    intro v
    by_cases hv : v = 0
    · subst hv; rfl
    · exact SimpleGraph.Adj.reachable (Or.inl ⟨rfl, hv⟩)
  exact ⟨fun u v => (h0 u).symm.trans (h0 v)⟩

lemma st_card : St.edgeFinset.card = 3 := by decide

lemma st_acyc : St.IsAcyclic := by
  have ht : St.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨st_conn, ?_⟩
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, st_card]
    simp
  exact ht.isAcyclic

def C3 : Circuit :=
  { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.and, [0, 5]⟩], output := 6 }

lemma c3_eval (x : Fin 4 → Bool) :
    C3.eval (List.ofFn x) = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) := by
  have h : x = ![x 0, x 1, x 2, x 3] := by
    funext i; fin_cases i <;> rfl
  rw [h]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  revert b0 b1 b2 b3
  decide

lemma fun_eq : (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) =
    (fun x : Fin 4 → Bool => decide (∃ i j : Fin 4, St.Adj i j ∧ x i = true ∧ x j = true)) := by
  funext x
  have h : x = ![x 0, x 1, x 2, x 3] := by
    funext i; fin_cases i <;> rfl
  rw [h]
  generalize x 0 = b0
  generalize x 1 = b1
  generalize x 2 = b2
  generalize x 3 = b3
  revert b0 b1 b2 b3
  decide

end PEqualNP.Outside.L_meta_746

open PEqualNP.Outside.L_meta_746 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_746 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3)) s ↔ 3 ≤ s := by
  intro s
  constructor
  · intro hs
    rw [fun_eq] at hs
    have := PEqualNP.MetaComplexity.L104 4 1 s St st_acyc ⟨0, 1, Or.inl ⟨rfl, by decide⟩⟩
      (fun T hT => by
        have := hT 0 1 (Or.inl ⟨rfl, by decide⟩)
        exact Finset.card_pos.mpr (by rcases this with h | h <;> exact ⟨_, h⟩)) hs
    rw [st_card] at this
    omega
  · intro hs
    refine ⟨C3, ?_, by simp [C3, Circuit.size]; omega, c3_eval⟩
    intro g hg
    simp only [C3, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h <;> subst h <;> simp
