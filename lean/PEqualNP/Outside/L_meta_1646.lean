import Mathlib
import PEqualNP.Defs

open Finset

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  intro n G _ noSquare U edges x Y marked R π blocks covered
  classical
  have pack (S : Finset (Fin n)) (sub : S ⊆ R) (neighbors : ∀ a ∈ S, G.Adj x a)
      (oneExtra : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → a ∈ Y ∨ b ∈ Y) : S.card ≤ π.card := by
    have coverS (a : S) := covered a.val (sub a.property)
    choose f hf ha using coverS
    let assign : S → π := fun a => ⟨f a,hf a⟩
    have inj : Function.Injective assign := by
      intro a b eq
      apply Subtype.ext
      by_contra ne
      have same : f a = f b := congrArg Subtype.val eq
      have h₁ := ha a
      have h₂ : b.val ∈ f a := same.symm ▸ ha b
      rcases (blocks _ (hf a)).2 with singleton | ⟨_,c,common,unmarked⟩
      · exact ne (card_le_one.mp singleton.le _ h₁ _ h₂)
      · have diff : x ≠ c := by
          rintro rfl
          rcases oneExtra a a.property b b.property ne with h | h
          · exact unmarked _ h₁ (marked _ h)
          · exact unmarked _ h₂ (marked _ h)
        have bound := noSquare x c diff
        exact ne (card_le_one.mp bound _
          (mem_filter.mpr ⟨mem_univ _,neighbors _ a.property,common _ h₁⟩) _
          (mem_filter.mpr ⟨mem_univ _,neighbors _ b.property,common _ h₂⟩))
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective assign inj
  constructor
  · apply pack (R ∩ Y) inter_subset_left
    · intro a ha
      exact edges _ (marked _ (mem_inter.mp ha).2)
    · intro a ha b _ _
      exact Or.inl (mem_inter.mp ha).2
  · intro all missing
    obtain ⟨r,hr,hy⟩ := not_subset.mp missing
    have extra : r ∉ R ∩ Y := fun h => hy (mem_inter.mp h).2
    rw [← card_insert_of_notMem extra]
    apply pack
    · exact insert_subset hr inter_subset_left
    · intro a ha
      exact all _ ((insert_subset hr (inter_subset_left (s₁:=R) (s₂:=Y))) ha)
    · intro a ha b hb ne
      rcases mem_insert.mp ha with rfl | h
      · rcases mem_insert.mp hb with e | h
        · exact (ne e.symm).elim
        · exact Or.inr (mem_inter.mp h).2
      · exact Or.inl (mem_inter.mp h).2
