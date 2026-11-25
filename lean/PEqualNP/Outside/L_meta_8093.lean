import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8093

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8093

theorem PEqualNP.Outside.L_meta_8093 : ∀ (x1 x2 x3 : ℕ) (x4 : Finset (Fin x1 × Fin x2)),   ∃ (x5 : Finset (Fin x1)) (x6 : Finset (Fin x2)),     have x7 : Finset (Fin x1 × Fin x2) := {x7 ∈ x4 | x7.1 ∈ x5 ∧ x7.2 ∈ x6};     x4.card + x3 * (x5.card + x6.card) ≤ x7.card + x3 * ((Finset.image Prod.fst x4).card + (Finset.image Prod.snd x4).card) ∧ ∀ x8 ⊆ x5, ∀ x10 ⊆ x6, {x12 ∈ x7 | x12.1 ∈ x8 ∧ x12.2 ∈ x10}.card + x3 * ((x5 \ x8).card + (x6 \ x10).card) ≤ x7.card := by
  intro n m k E
  classical
  obtain ⟨⟨A, B⟩, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin n) × Finset (Fin m)))
    (fun p => ((E.filter fun e => e.1 ∈ p.1 ∧ e.2 ∈ p.2).card : ℤ) - k * ((p.1.card : ℤ) + p.2.card)) ⟨(∅, ∅), Finset.mem_univ _⟩
  refine ⟨A, B, ?_, ?_⟩
  · have h := hmax (Finset.image Prod.fst E, Finset.image Prod.snd E) (Finset.mem_univ _)
    have e : (E.filter fun e => e.1 ∈ Finset.image Prod.fst E ∧ e.2 ∈ Finset.image Prod.snd E) = E := by
      rw [Finset.filter_eq_self]
      intro e he
      exact ⟨Finset.mem_image_of_mem _ he, Finset.mem_image_of_mem _ he⟩
    simp only [e] at h
    zify
    linarith
  · intro A' hA B' hB
    have h := hmax (A', B') (Finset.mem_univ _)
    have e : ((E.filter fun e => e.1 ∈ A ∧ e.2 ∈ B).filter fun e => e.1 ∈ A' ∧ e.2 ∈ B') = E.filter fun e => e.1 ∈ A' ∧ e.2 ∈ B' := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, hA h2.1, hB h2.2⟩, h2⟩
    have c1 := Finset.card_sdiff_add_card_eq_card hA
    have c2 := Finset.card_sdiff_add_card_eq_card hB
    simp only [e]
    simp only at h
    zify at c1 c2 ⊢
    rw [← c1, ← c2] at h
    linarith
