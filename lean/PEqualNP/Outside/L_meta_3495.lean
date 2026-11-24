import Mathlib.Data.Fintype.Card

theorem PEqualNP.Outside.L_meta_3495 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ (x9 x10 : Fin x2 → Prop), (∀ (x11 x12 : Fin x2), x3 x11 x12 → x9 x11 ∨ x10 x12) → (∀ (x12 : Fin x2), x9 x12 → ∃ x14 ∈ x7, x3 x12 x14) → (∀ x13 ∈ x7, ¬x10 x13) → (∀ (x14 : Fin x2), x9 x14 ↔ ∃ x15 ∈ x7, x3 x14 x15) ∧ ∀ (x14 : Fin x2), x10 x14 ↔ x14 ∉ x7 := by
  classical
  intro q n I inst hcount hpair S hsize A B hcover hinside havoid
  constructor
  · intro p
    constructor
    · exact hinside p
    · rintro ⟨s, hs, hps⟩
      exact (hcover p s hps).resolve_right (havoid s hs)
  · intro l
    constructor
    · intro hl hs
      exact havoid l hs hl
    · intro hout
      by_contra hnot
      have pick (p : {p : Fin n // I p l}) : ∃ s : ↥S, I p.val s.val := by
        obtain ⟨s, hs, hps⟩ := hinside p.val ((hcover p.val l p.property).resolve_right hnot)
        exact ⟨⟨s, hs⟩, hps⟩
      let f (p : {p : Fin n // I p l}) : ↥S := Classical.choose (pick p)
      have hf (p : {p : Fin n // I p l}) : I p.val (f p).val :=
        Classical.choose_spec (pick p)
      have hinj : Function.Injective f := by
        intro p r eq
        apply Subtype.ext
        by_contra hne
        obtain ⟨m, _, hu⟩ := hpair p.val r.val hne
        have hl : l = m := hu l ⟨p.property, r.property⟩
        have hr : I r.val (f p).val := by
          rw [eq]
          exact hf r
        have hs : (f p).val = m := hu _ ⟨hf p, hr⟩
        exact hout ((hs.trans hl.symm) ▸ (f p).property)
      have hcard := Fintype.card_le_of_injective f hinj
      rw [hcount l, Fintype.card_coe] at hcard
      exact (Nat.not_succ_le_self q) (hcard.trans hsize)
