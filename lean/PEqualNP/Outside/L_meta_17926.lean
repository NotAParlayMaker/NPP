import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17926 :
∀ (x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ))) (x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool), (∀ (x3 x4 x5 x6 : Finset (Fin (13 : ℕ))), x3 ⊆ x4 → x5 ⊆ x6 → x2 x3 x5 = Bool.true → x2 x4 x6 = Bool.true) → (∀ (x4 x5 : Fin (13 : ℕ)), x4 ∈ x1 x5 → x2 {x4} {x5} = Bool.true) → x2 Finset.univ ∅ = Bool.false → (∀ (x6 : Fin (13 : ℕ)), x2 (x1 x6)ᶜ {x6} = Bool.false) → ∀ (x7 x8 : Finset (Fin (13 : ℕ))), x8.card ≤ (1 : ℕ) → (x2 x7 x8 = Bool.true ↔ ∃ x10 ∈ x7, ∃ x11 ∈ x8, x10 ∈ x1 x11) := by
  intro S f mono yes no0 no1 P L one
  constructor
  · intro ht
    by_contra miss
    by_cases empty : L = ∅
    · subst L
      have hf := mono P Finset.univ ∅ ∅ (Finset.subset_univ _) (by rfl) ht
      simp [no0] at hf
    · obtain ⟨l,hl⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      have all : L ⊆ {l} := by
        intro k hk
        have eq := (Finset.card_le_one.mp one) k hk l hl
        simpa using eq
      have cover : P ⊆ (S l)ᶜ := by
        intro p hp
        exact Finset.mem_compl.mpr (fun inc => miss ⟨p,hp,l,hl,inc⟩)
      have hf := mono P (S l)ᶜ L {l} cover all ht
      simp [no1] at hf
  · rintro ⟨p,hp,l,hl,inc⟩
    exact mono {p} P {l} L (Finset.singleton_subset_iff.mpr hp)
      (Finset.singleton_subset_iff.mpr hl) (yes p l inc)
