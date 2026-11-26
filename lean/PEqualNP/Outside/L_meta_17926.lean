import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17926 : ∀ (x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ))) (x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool), (∀ (x3 x4 x5 x6 : Finset (Fin (13 : ℕ))), x3 ⊆ x4 → x5 ⊆ x6 → x2 x3 x5 = Bool.true → x2 x4 x6 = Bool.true) → (∀ (x4 x5 : Fin (13 : ℕ)), x4 ∈ x1 x5 → x2 {x4} {x5} = Bool.true) → x2 Finset.univ ∅ = Bool.false → (∀ (x6 : Fin (13 : ℕ)), x2 (x1 x6)ᶜ {x6} = Bool.false) → ∀ (x7 x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (1 : ℕ) → (x2 x7 x8 = Bool.true ↔ ∃ x10 ∈ x7, ∃ x11 ∈ x8, x10 ∈ x1 x11) := by
  intro L f hm hs hu hc P Q hQ
  rcases Finset.card_le_one_iff_subset_singleton.mp hQ with ⟨l, hl⟩
  rcases Finset.subset_singleton_iff.mp hl with h | h
  · subst h
    constructor
    · intro hf
      have := hm P Finset.univ ∅ ∅ (Finset.subset_univ _) (le_refl _) hf
      rw [hu] at this
      exact absurd this (by decide)
    · rintro ⟨p, _, q, hq, _⟩
      simp at hq
  · subst h
    constructor
    · intro hf
      by_contra hn
      push_neg at hn
      have hsub : P ⊆ (L l)ᶜ := by
        intro p hp
        rw [Finset.mem_compl]
        exact hn p hp l (Finset.mem_singleton_self l)
      have := hm P (L l)ᶜ {l} {l} hsub (le_refl _) hf
      rw [hc] at this
      exact absurd this (by decide)
    · rintro ⟨p, hp, q, hq, hpq⟩
      rw [Finset.mem_singleton] at hq
      subst hq
      exact hm {p} P {q} {q} (Finset.singleton_subset_iff.mpr hp) (le_refl _) (hs p q hpq)
