import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8093 : ∀ (x1 x2 x3 : ℕ) (x4 : Finset (Fin x1 × Fin x2)),   ∃ (x5 : Finset (Fin x1)) (x6 : Finset (Fin x2)),     have x7 : Finset (Fin x1 × Fin x2) := {x7 ∈ x4 | x7.1 ∈ x5 ∧ x7.2 ∈ x6};     x4.card + x3 * (x5.card + x6.card) ≤ x7.card + x3 * ((Finset.image Prod.fst x4).card + (Finset.image Prod.snd x4).card) ∧ ∀ x8 ⊆ x5, ∀ x10 ⊆ x6, {x12 ∈ x7 | x12.1 ∈ x8 ∧ x12.2 ∈ x10}.card + x3 * ((x5 \ x8).card + (x6 \ x10).card) ≤ x7.card := by
  intro x1 x2 x3 x4
  obtain ⟨⟨A, B⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin x1) × Finset (Fin x2)))
    (fun p => ({x ∈ x4 | x.1 ∈ p.1 ∧ x.2 ∈ p.2}).card + x3 * ((p.1)ᶜ.card + (p.2)ᶜ.card)) Finset.univ_nonempty
  refine ⟨A, B, ?_, ?_⟩
  · have h := hmax (Finset.image Prod.fst x4, Finset.image Prod.snd x4) (Finset.mem_univ _)
    have he : ({x ∈ x4 | x.1 ∈ Finset.image Prod.fst x4 ∧ x.2 ∈ Finset.image Prod.snd x4}) = x4 := by
      apply Finset.filter_true_of_mem
      intro x hx
      exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
    simp only [he] at h
    have e1 := Finset.card_add_card_compl A
    have e2 := Finset.card_add_card_compl B
    have e3 := Finset.card_add_card_compl (Finset.image Prod.fst x4)
    have e4 := Finset.card_add_card_compl (Finset.image Prod.snd x4)
    show x4.card + x3 * (A.card + B.card) ≤ ({x ∈ x4 | x.1 ∈ A ∧ x.2 ∈ B}).card + x3 * ((Finset.image Prod.fst x4).card + (Finset.image Prod.snd x4).card)
    nlinarith
  · intro x8 h8 x10 h10
    have h := hmax (x8, x10) (Finset.mem_univ _)
    have he : ({x ∈ ({x ∈ x4 | x.1 ∈ A ∧ x.2 ∈ B}) | x.1 ∈ x8 ∧ x.2 ∈ x10}) = ({x ∈ x4 | x.1 ∈ x8 ∧ x.2 ∈ x10}) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h8 h2, h10 h3⟩, h2, h3⟩
    have e1 := Finset.card_add_card_compl A
    have e2 := Finset.card_add_card_compl B
    have e3 := Finset.card_add_card_compl x8
    have e4 := Finset.card_add_card_compl x10
    have s1 := Finset.card_sdiff_add_card_eq_card h8
    have s2 := Finset.card_sdiff_add_card_eq_card h10
    show ({x ∈ ({x ∈ x4 | x.1 ∈ A ∧ x.2 ∈ B}) | x.1 ∈ x8 ∧ x.2 ∈ x10}).card + x3 * ((A \ x8).card + (B \ x10).card) ≤ ({x ∈ x4 | x.1 ∈ A ∧ x.2 ∈ B}).card
    rw [he]
    simp only at h
    nlinarith
