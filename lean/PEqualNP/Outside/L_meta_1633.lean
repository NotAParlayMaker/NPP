import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1633 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ t u : Fin N, t ≠ i0 → u ≠ i0 → t ≠ u →
      ((∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) ↔ ((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L u ∧ p0 ∉ L u)) ∨ ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L u ∧ p1 ∉ L u))) := by
  intro q N L i0 p0 p1 hq hN hcard hint hjoin h01 hp0 hp1 T hT t u ht hu htu
  have nb : ∀ s : Fin N, s ≠ i0 → p0 ∈ L s → p1 ∈ L s → False := by
    intro s hs a b
    have h1 := hint s i0 hs
    rw [Finset.card_eq_one] at h1
    obtain ⟨c, hc⟩ := h1
    have e0 : p0 ∈ L s ∩ L i0 := Finset.mem_inter.mpr ⟨a, hp0⟩
    have e1 : p1 ∈ L s ∩ L i0 := Finset.mem_inter.mpr ⟨b, hp1⟩
    rw [hc, Finset.mem_singleton] at e0 e1
    exact h01 (e0.trans e1.symm)
  have ex : ∀ a b : Fin N, a ≠ b → ∀ x : Fin N, ∃ p ∈ L a \ L b, p ≠ x := by
    intro a b hab x
    have h1 := hint a b hab
    have h2 := Finset.card_sdiff_add_card_inter (L a) (L b)
    have h3 := hcard a
    exact Finset.exists_mem_ne (by omega) x
  constructor
  · rintro ⟨⟨p, hp, v, hv, h1⟩, ⟨p', hp', v', hv', h2⟩⟩
    rw [hT] at h1 h2
    rw [Finset.mem_sdiff] at hp hp'
    rcases h1 with e | ⟨a, b, e⟩ | ⟨a, b, c, e⟩ | ⟨a, b, _⟩
    · rw [e] at hv; exact absurd hv hp.2
    · rw [e] at hv
      rcases h2 with e' | ⟨a', b', e'⟩ | ⟨a', b', c', e'⟩ | ⟨a', b', _⟩
      · rw [e'] at hv'; exact absurd hv' hp'.2
      · exact absurd hv a'
      · rw [e'] at hv'
        exact Or.inr ⟨⟨hv', a⟩, ⟨hv, b'⟩⟩
      · exact (nb u hu a' b').elim
    · rw [e] at hv
      rcases h2 with e' | ⟨a', b', e'⟩ | ⟨a', b', c', e'⟩ | ⟨a', b', _⟩
      · rw [e'] at hv'; exact absurd hv' hp'.2
      · exact Or.inl ⟨⟨a, b⟩, ⟨hv, a'⟩⟩
      · rw [e'] at hv'; exact absurd hv' b
      · exact (nb u hu a' b').elim
    · exact (nb t ht a b).elim
  · rintro (⟨⟨a, b⟩, ⟨c, d⟩⟩ | ⟨⟨a, b⟩, ⟨c, d⟩⟩)
    · obtain ⟨p, hp, hpne⟩ := ex t u htu p0
      obtain ⟨p', hp', hpne'⟩ := ex u t (Ne.symm htu) p1
      exact ⟨⟨p, hp, p1, c, (hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨a, b, hpne, rfl⟩)))⟩,
        ⟨p', hp', p0, a, (hT u p' p0).mpr (Or.inr (Or.inl ⟨d, hpne', rfl⟩))⟩⟩
    · obtain ⟨p, hp, hpne⟩ := ex t u htu p1
      obtain ⟨p', hp', hpne'⟩ := ex u t (Ne.symm htu) p0
      exact ⟨⟨p, hp, p0, c, (hT t p p0).mpr (Or.inr (Or.inl ⟨b, hpne, rfl⟩))⟩,
        ⟨p', hp', p1, a, (hT u p' p1).mpr (Or.inr (Or.inr (Or.inl ⟨c, d, hpne', rfl⟩)))⟩⟩
