import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1630 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    (∀ x y : Fin N → Bool, (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) → (∀ v : Fin N, x v = true → y v = true) → (y p0 = true ∨ y p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → y u = true)) ∧
    (∀ t : Fin N, ((fun v : Fin N => decide (v ∉ L t)) p0 = true ∨ (fun v : Fin N => decide (v ∉ L t)) p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) u = true)) ∧
    (∀ t : Fin N, ∀ p ∈ L t, (T t p p0 = true ∨ T t p p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → T t p u = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, decide (v ∉ L t) = true) = false ∧ ∀ p ∈ L t, decide (∃ v ∈ L t, T t p v = true) = true) := by
  classical
  intro q N L i0 p0 p1 _ _ _ hmeet _ h01 h0 h1 T hT
  have nb : ∀ s : Fin N, p0 ∈ L s → p1 ∈ L s → s = i0 := by
    intro s a b
    by_contra hs
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L s ∩ L i0 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.2 ⟨a, h0⟩
      · exact Finset.mem_inter.2 ⟨b, h1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair h01, hmeet s i0 hs] at this
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h hxy
    rcases h with h | h | h
    · exact Or.inl (hxy p0 h)
    · exact Or.inr (Or.inl (hxy p1 h))
    · exact Or.inr (Or.inr fun u hu => hxy u (h u hu))
  · intro t
    by_cases ha : p0 ∈ L t
    · by_cases hb : p1 ∈ L t
      · have := nb t ha hb
        subst this
        exact Or.inr (Or.inr fun u hu => by simpa using hu)
      · exact Or.inr (Or.inl (by simpa using hb))
    · exact Or.inl (by simpa using ha)
  · intro t p _
    by_cases ha : p0 ∈ L t
    · by_cases hb : p1 ∈ L t
      · have := nb t ha hb
        subst this
        by_cases hp0 : p = p0
        · exact Or.inl ((hT t p p0).2 (Or.inl hp0.symm))
        · by_cases hp1 : p = p1
          · exact Or.inr (Or.inl ((hT t p p1).2 (Or.inl hp1.symm)))
          · exact Or.inr (Or.inr fun u hu =>
              (hT t p u).2 (Or.inr (Or.inr (Or.inr ⟨ha, hb, hp0, hp1, hu⟩))))
      · by_cases hp0 : p = p0
        · exact Or.inl ((hT t p p0).2 (Or.inl hp0.symm))
        · exact Or.inr (Or.inl ((hT t p p1).2 (Or.inr (Or.inr (Or.inl ⟨ha, hb, hp0, rfl⟩)))))
    · by_cases hp1 : p = p1
      · exact Or.inr (Or.inl ((hT t p p1).2 (Or.inl hp1.symm)))
      · exact Or.inl ((hT t p p0).2 (Or.inr (Or.inl ⟨ha, hp1, rfl⟩)))
  · intro t
    refine ⟨by simp, fun p hp => ?_⟩
    exact decide_eq_true ⟨p, hp, (hT t p p).2 (Or.inl rfl)⟩
