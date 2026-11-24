import Mathlib

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
  intro q N L i0 p0 p1 hq hN hcard hinter hpoints hne hp0 hp1 T hT
  have line_eq (t : Fin N) (h0 : p0 ∈ L t) (h1 : p1 ∈ L t) : t = i0 := by
    by_contra ht
    have hc : (L i0 ∩ L t).card ≤ 1 := by rw [hinter i0 t (Ne.symm ht)]
    exact hne (Finset.card_le_one.mp hc p0 (Finset.mem_inter.mpr ⟨hp0, h0⟩)
      p1 (Finset.mem_inter.mpr ⟨hp1, h1⟩))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with h0 | h1 | hall
    · exact Or.inl (hxy p0 h0)
    · exact Or.inr (Or.inl (hxy p1 h1))
    · exact Or.inr (Or.inr fun u hu => hxy u (hall u hu))
  · intro t
    by_cases h0 : p0 ∈ L t
    · by_cases h1 : p1 ∈ L t
      · have ht := line_eq t h0 h1
        subst t
        exact Or.inr (Or.inr fun u hu => by simpa using hu)
      · exact Or.inr (Or.inl (by simpa using h1))
    · exact Or.inl (by simpa using h0)
  · intro t p hp
    by_cases he0 : p = p0
    · left; apply (hT t p p0).mpr; exact Or.inl he0.symm
    · by_cases he1 : p = p1
      · right; left; apply (hT t p p1).mpr; exact Or.inl he1.symm
      · by_cases h0 : p0 ∈ L t
        · by_cases h1 : p1 ∈ L t
          · have ht := line_eq t h0 h1
            right; right
            intro u hu
            apply (hT t p u).mpr
            exact Or.inr (Or.inr (Or.inr ⟨h0, h1, he0, he1, ht.symm ▸ hu⟩))
          · right; left
            exact (hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨h0, h1, he0, rfl⟩)))
        · left
          exact (hT t p p0).mpr (Or.inr (Or.inl ⟨h0, he1, rfl⟩))
  · intro t
    constructor
    · simp
    · intro p hp
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, (hT t p p).mpr (Or.inl rfl)⟩