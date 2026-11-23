import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_752

private def adjacent (a b : Fin 4) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)

private def graph : SimpleGraph (Fin 4) where
  Adj := adjacent
  symm := ⟨by
    intro a b h
    unfold adjacent at *
    tauto⟩
  loopless := ⟨by
    intro a
    fin_cases a <;> simp [adjacent]⟩

private def adjDec : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable
    ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2)))

private lemma acyclic : graph.IsAcyclic := by
  refine SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mpr ?_
  intro a b hab
  apply SimpleGraph.not_reachable_of_neighborSet_right_eq_empty (SimpleGraph.Adj.ne hab)
  ext x
  change (graph.deleteEdges {s(a, b)}).Adj b x ↔ False
  have : graph.Adj b x → x = a := by
    change adjacent a b at hab
    change adjacent b x → x = a
    fin_cases a <;> fin_cases b <;> fin_cases x <;> revert hab <;> simp [adjacent]
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, iff_false]
  rintro ⟨h, hn⟩
  have hx := this h
  subst x
  exact hn Sym2.eq_swap

private lemma cover_lower (T : Finset (Fin 4))
    (h : ∀ i j : Fin 4, graph.Adj i j → i ∈ T ∨ j ∈ T) : 2 ≤ T.card := by
  obtain h₀ | h₁ := h 0 1 (by exact Or.inl ⟨rfl, rfl⟩) <;>
    obtain h₂ | h₃ := h 2 3 (by exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · exact Finset.one_lt_card.mpr ⟨0, h₀, 2, h₂, by decide⟩
  · exact Finset.one_lt_card.mpr ⟨0, h₀, 3, h₃, by decide⟩
  · exact Finset.one_lt_card.mpr ⟨1, h₁, 2, h₂, by decide⟩
  · exact Finset.one_lt_card.mpr ⟨1, h₁, 3, h₃, by decide⟩

private lemma result (s : ℕ) :
    HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s := by
  letI := adjDec
  have hfun : (fun x : Fin 4 → Bool =>
      decide (∃ i j : Fin 4, graph.Adj i j ∧ x i = true ∧ x j = true)) =
      (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) := by decide
  have hedge : ∃ i j : Fin 4, graph.Adj i j := ⟨0, 1, Or.inl ⟨rfl, rfl⟩⟩
  have hcard : graph.edgeFinset.card = 2 := by decide
  rw [← hfun]
  constructor
  · intro h
    have hb := L104 4 2 s graph acyclic hedge cover_lower h
    omega
  · intro hs
    let T : Finset (Fin 4) := {0, 2}
    have hc : ∀ i j : Fin 4, graph.Adj i j → i ∈ T ∨ j ∈ T := by decide
    have ht : T.card = 2 := by decide
    obtain ⟨C, hfan, hsize, heval⟩ := L105 4 graph T hedge hc
    exact ⟨C, hfan, by omega, heval⟩

end PEqualNP.Outside.L_meta_752

theorem PEqualNP.Outside.L_meta_752 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 2 && x 3)) s ↔ 3 ≤ s :=
  PEqualNP.Outside.L_meta_752.result
