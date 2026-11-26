import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17926 : (∀ (x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ))) (x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool), (∀ (x3 x4 x5 x6 : Finset (Fin (13 : ℕ))), x3 ⊆ x4 → x5 ⊆ x6 → x2 x3 x5 = Bool.true → x2 x4 x6 = Bool.true) → (∀ (x4 x5 : Fin (13 : ℕ)), x4 ∈ x1 x5 → x2 {x4} {x5} = Bool.true) → x2 Finset.univ ∅ = Bool.false → (∀ (x6 : Fin (13 : ℕ)), x2 (x1 x6)ᶜ {x6} = Bool.false) → ∀ (x7 x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (1 : ℕ) → (x2 x7 x8 = Bool.true ↔ ∃ x10 ∈ x7, ∃ x11 ∈ x8, x10 ∈ x1 x11)) := by
  intro L f hmono hinc hemp hcomp P Q hQ
  constructor
  · intro hf
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hQ with h0 | h1
    · rw [Finset.card_eq_zero] at h0
      subst h0
      have hbad := hmono P Finset.univ ∅ ∅ (Finset.subset_univ P) (Finset.Subset.refl ∅) hf
      rw [hemp] at hbad
      cases hbad
    · obtain ⟨l, rfl⟩ := Finset.card_eq_one.mp h1
      by_contra hno
      have hsub : P ⊆ (L l)ᶜ := by
        intro p hp
        rw [Finset.mem_compl]
        intro hpl
        exact hno ⟨p, hp, l, Finset.mem_singleton_self l, hpl⟩
      have hbad := hmono P (L l)ᶜ {l} {l} hsub (Finset.Subset.refl {l}) hf
      rw [hcomp l] at hbad
      cases hbad
  · rintro ⟨p, hp, l, hl, hpl⟩
    exact hmono {p} P {l} Q (Finset.singleton_subset_iff.mpr hp)
      (Finset.singleton_subset_iff.mpr hl) (hinc p l hpl)
