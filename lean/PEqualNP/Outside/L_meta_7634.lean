import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7634 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → ∀ (x9 x10 : Fin x2), x3 x9 x10 → ((Finset.filter (x3 x9) Finset.univ).erase x10).card = x1 ∧ ∃ (x12 : Fin x2 → Fin x2), ∀ (x13 x14 : Fin x2), x13 ≠ x9 → x3 x9 x14 → (x3 x13 x14 ↔ x12 x13 = x14) := by
  intro x1 x2 x3 x4 hpos hx2 h1 h2 x9 x10 h910
  subst hx2
  classical
  have hf : ∃ f : Fin (x1 ^ 2 + x1 + 1) → Fin (x1 ^ 2 + x1 + 1), ∀ x13, x13 ≠ x9 → (x3 x13 (f x13) ∧ x3 x9 (f x13)) ∧ ∀ y, x3 x13 y ∧ x3 x9 y → y = f x13 := by
    refine ⟨fun x13 => if h : x13 = x9 then x9 else Classical.choose (h2 x13 x9 h), ?_⟩
    intro x13 h
    simp only [dif_neg h]
    exact Classical.choose_spec (h2 x13 x9 h)
  obtain ⟨f, hf⟩ := hf
  have key : ∀ x13 x14, x13 ≠ x9 → x3 x9 x14 → (x3 x13 x14 ↔ f x13 = x14) := by
    intro x13 x14 hne h14
    constructor
    · intro h; exact ((hf x13 hne).2 x14 ⟨h, h14⟩).symm
    · intro h; subst h; exact (hf x13 hne).1.1
  refine ⟨?_, f, key⟩
  have hmaps : ∀ p ∈ Finset.univ.erase x9, f p ∈ Finset.filter (x3 x9) Finset.univ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hf p (Finset.ne_of_mem_erase hp)).1.2
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ l ∈ Finset.filter (x3 x9) Finset.univ, (Finset.filter (fun p => f p = l) (Finset.univ.erase x9)).card = x1 := by
    intro l hl
    have hl' : x3 x9 l := by simpa using hl
    have hE : Finset.filter (fun p => f p = l) (Finset.univ.erase x9) = (Finset.filter (fun p => x3 p l) Finset.univ).erase x9 := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      constructor
      · rintro ⟨hne, h⟩; exact ⟨hne, (key p l hne hl').2 h⟩
      · rintro ⟨hne, h⟩; exact ⟨hne, (key p l hne hl').1 h⟩
    rw [hE, Finset.card_erase_of_mem (by simpa using hl')]
    have h1l := h1 l
    rw [Fintype.card_subtype] at h1l
    omega
  rw [Finset.sum_congr rfl hfib, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, Finset.sum_const, smul_eq_mul] at hsum
  have hL : (Finset.filter (x3 x9) Finset.univ).card = x1 + 1 := by
    have h2 : (Finset.filter (x3 x9) Finset.univ).card * x1 = (x1 + 1) * x1 := by
      rw [← hsum]; simp; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  rw [Finset.card_erase_of_mem (by simpa using h910), hL]
  simp
