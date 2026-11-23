import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L105
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_754

open SimpleGraph
open PEqualNP.MetaComplexity

abbrev G : SimpleGraph (Fin 5) where
  Adj i j :=
    (i = 0 ∧ (j = 1 ∨ j = 2 ∨ j = 3)) ∨
    (j = 0 ∧ (i = 1 ∨ i = 2 ∨ i = 3)) ∨
    (i = 1 ∧ j = 4) ∨
    (j = 1 ∧ i = 4)
  symm := ⟨by
    intro i j h
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by
    intro i h
    rcases h with ⟨rfl, h | h | h⟩ | ⟨rfl, h | h | h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp at h⟩

abbrev ef (x : Fin 5 → Bool) : Bool :=
  decide (∃ i j : Fin 5, G.Adj i j ∧ x i = true ∧ x j = true)

theorem firstEdge : G.Adj 0 1 := by decide

theorem connectedG : G.Connected := by
  have r : ∀ i : Fin 5, G.Reachable 0 i := by
    intro i
    fin_cases i
    · exact SimpleGraph.Reachable.refl _
    · exact firstEdge.reachable
    · exact (show G.Adj 0 2 by decide).reachable
    · exact (show G.Adj 0 3 by decide).reachable
    · exact firstEdge.reachable.trans (show G.Adj 1 4 by decide).reachable
  exact ⟨fun a b => (r a).symm.trans (r b)⟩

theorem edgeFinset_eq :
    G.edgeFinset = ({s(0, 1), s(0, 2), s(0, 3), s(1, 4)} : Finset (Sym2 (Fin 5))) := by
  ext e
  induction e using Sym2.ind with
  | _ i j =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · intro h
      rcases h with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))
      · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · intro h
      rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

theorem edgesG : G.edgeFinset.card = 4 := by
  rw [edgeFinset_eq]
  decide

theorem forestG : G.IsAcyclic := by
  apply SimpleGraph.IsTree.isAcyclic
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connectedG, ?_⟩
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, edgesG, Nat.card_fin]

abbrev T : Finset (Fin 5) := {0, 1}

theorem coverG : ∀ i j : Fin 5, G.Adj i j → i ∈ T ∨ j ∈ T := by
  intro i j h
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [T]

theorem two_le_card {S : Finset (Fin 5)} {a b : Fin 5} (hne : a ≠ b) (ha : a ∈ S) (hb : b ∈ S) :
    2 ≤ S.card := by
  have hsub : {a, b} ⊆ S := Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
  have hcard : ({a, b} : Finset (Fin 5)).card = 2 := Finset.card_pair hne
  exact hcard ▸ Finset.card_le_card hsub

theorem lowerCover : ∀ S : Finset (Fin 5), (∀ i j : Fin 5, G.Adj i j → i ∈ S ∨ j ∈ S) → 2 ≤ S.card := by
  intro S hS
  rcases hS 0 2 (by decide) with ha | ha <;> rcases hS 1 4 (by decide) with hb | hb
  · exact two_le_card (by decide) ha hb
  · exact two_le_card (by decide) ha hb
  · exact two_le_card (by decide) ha hb
  · exact two_le_card (by decide) ha hb

theorem evalG (x : Fin 5 → Bool) :
    ef x = ((x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) := by
  rw [ef, Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    rcases hij with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Or.inl (Or.inl ⟨hi, hj⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hi, hj⟩))
    · exact Or.inl (Or.inr ⟨hi, hj⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨hj, hi⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hj, hi⟩))
    · exact Or.inl (Or.inr ⟨hj, hi⟩)
    · exact Or.inr ⟨hi, hj⟩
    · exact Or.inr ⟨hj, hi⟩
  · rintro (((⟨h0, h1⟩ | ⟨h0, h2⟩) | ⟨h0, h3⟩) | ⟨h1, h4⟩)
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 2, by decide, h0, h2⟩
    · exact ⟨0, 3, by decide, h0, h3⟩
    · exact ⟨1, 4, by decide, h1, h4⟩

theorem main : ∀ s : ℕ, HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 5 ≤ s := by
  intro s
  rw [← funext evalG]
  constructor
  · intro h
    have hb := L104 5 2 s G forestG ⟨0, 1, firstEdge⟩ lowerCover h
    rw [edgesG] at hb
    omega
  · intro hs
    have hu := L105 5 G T ⟨0, 1, firstEdge⟩ coverG
    have ct : T.card = 2 := by decide
    rw [edgesG, ct] at hu
    obtain ⟨C, ho, hl, he⟩ := hu
    exact ⟨C, ho, hl.trans hs, he⟩

end PEqualNP.Outside.L_meta_754

theorem PEqualNP.Outside.L_meta_754 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 5 (fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4)) s ↔ 5 ≤ s := by
  exact PEqualNP.Outside.L_meta_754.main
