import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7057 : ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1 → Prop) [x3 : DecidableRel x2], (∀ (x4 x5 : Fin x1), x4 ≠ x5 → ∃! x7 : Fin x1, x2 x4 x7 ∧ x2 x5 x7) → ∀ (x5 : Fin x1) (x6 : Finset (Fin x1)), x5 ∉ x6 → Fintype.card { x8 : Fin x1 // x2 x8 x5 ∧ ∃ x9 ∈ x6, x2 x8 x9 } ≤ x6.card := by
  intro n R _ h l L hl
  rw [Fintype.card_subtype]
  calc (Finset.univ.filter (fun p => R p l ∧ ∃ l' ∈ L, R p l')).card
      ≤ (L.biUnion (fun l' => Finset.univ.filter (fun p => R p l ∧ R p l'))).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hp ⊢
        obtain ⟨hpl, l', hl', hpl'⟩ := hp
        exact ⟨l', hl', hpl, hpl'⟩
    _ ≤ ∑ l' ∈ L, (Finset.univ.filter (fun p => R p l ∧ R p l')).card := Finset.card_biUnion_le
    _ ≤ ∑ l' ∈ L, 1 := by
        apply Finset.sum_le_sum
        intro l' hl'
        rw [Finset.card_le_one]
        intro p hp q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        by_contra hpq
        obtain ⟨m, _, hm⟩ := h p q hpq
        have h1 := hm l ⟨hp.1, hq.1⟩
        have h2 := hm l' ⟨hp.2, hq.2⟩
        exact hl (by rw [h1, ← h2]; exact hl')
    _ = L.card := by simp
