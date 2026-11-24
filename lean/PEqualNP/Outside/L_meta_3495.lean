import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3495 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (∀ (x5 : Fin x2), Fintype.card { x6 : Fin x2 // x3 x6 x5 } = x1 + (1 : ℕ)) → (∀ (x6 x7 : Fin x2), x6 ≠ x7 → ∃! x9 : Fin x2, x3 x6 x9 ∧ x3 x7 x9) → ∀ (x7 : Finset (Fin x2)), x7.card ≤ x1 → ∀ (x9 x10 : Fin x2 → Prop), (∀ (x11 x12 : Fin x2), x3 x11 x12 → x9 x11 ∨ x10 x12) → (∀ (x12 : Fin x2), x9 x12 → ∃ x14 ∈ x7, x3 x12 x14) → (∀ x13 ∈ x7, ¬x10 x13) → (∀ (x14 : Fin x2), x9 x14 ↔ ∃ x15 ∈ x7, x3 x14 x15) ∧ ∀ (x14 : Fin x2), x10 x14 ↔ x14 ∉ x7 := by
  classical
  intro q n inc _ hdeg huniq S hS P Q hcover hP hnotQ
  constructor
  · intro p
    constructor
    · exact hP p
    · rintro ⟨s, hsS, hps⟩
      exact (hcover p s hps).resolve_right (hnotQ s hsS)
  · intro l
    constructor
    · intro hQl hlS
      exact hnotQ l hlS hQl
    · intro hlS
      by_contra hnQl
      have hPon : ∀ p : {p : Fin n // inc p l}, P p.val := by
        intro p
        exact (hcover p.val l p.property).resolve_right hnQl
      choose f hfS hfinc using fun p : {p : Fin n // inc p l} =>
        hP p.val (hPon p)
      let g : {p : Fin n // inc p l} → ↥S := fun p => ⟨f p, hfS p⟩
      have hcardgt : Fintype.card ↥S < Fintype.card {p : Fin n // inc p l} := by
        simpa [hdeg l] using hS
      obtain ⟨p, p', hne, hfg⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcardgt
      have hne' : p.val ≠ p'.val := by
        intro heq
        apply hne
        exact Subtype.ext heq
      have hff : f p = f p' := congrArg Subtype.val hfg
      obtain ⟨m, hm, huniq'⟩ := huniq p.val p'.val hne'
      have hboth : inc p.val (f p) ∧ inc p'.val (f p) :=
        ⟨hfinc p, by simpa [hff] using hfinc p'⟩
      have hfl : f p = l :=
        (huniq' (f p) hboth).trans (huniq' l ⟨p.property, p'.property⟩).symm
      have hlS' : l ∈ S := by
        rw [← hfl]
        exact hfS p
      exact hlS hlS'
