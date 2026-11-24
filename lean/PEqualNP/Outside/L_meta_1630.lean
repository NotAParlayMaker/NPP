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
  intro q N L i0 p0 p1 _ _ _ hint _ h01 hp0 hp1 T hT
  have key : ∀ t : Fin N, p0 ∈ L t → p1 ∈ L t → t = i0 := by
    intro t h0 h1
    by_contra hne
    have hc := hint t i0 hne
    have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨h0, hp0⟩
      · exact Finset.mem_inter.mpr ⟨h1, hp1⟩
    have h2 : ({p0, p1} : Finset (Fin N)).card = 2 := Finset.card_pair h01
    have h3 := Finset.card_le_card hsub
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with h | h | h
    · exact Or.inl (hxy _ h)
    · exact Or.inr (Or.inl (hxy _ h))
    · exact Or.inr (Or.inr (fun u hu => hxy _ (h u hu)))
  · intro t
    by_cases h0 : p0 ∈ L t
    · by_cases h1 : p1 ∈ L t
      · have ht := key t h0 h1
        subst ht
        right; right
        intro u hu
        simpa using hu
      · right; left
        simpa using h1
    · left
      simpa using h0
  · intro t p hp
    by_cases e0 : p = p0
    · left
      exact (hT t p p0).mpr (Or.inl e0.symm)
    by_cases e1 : p = p1
    · right; left
      exact (hT t p p1).mpr (Or.inl e1.symm)
    by_cases h0 : p0 ∈ L t
    · by_cases h1 : p1 ∈ L t
      · have ht := key t h0 h1
        subst ht
        right; right
        intro u hu
        exact (hT _ p u).mpr (Or.inr (Or.inr (Or.inr ⟨h0, h1, e0, e1, hu⟩)))
      · right; left
        exact (hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨h0, h1, e0, rfl⟩)))
    · left
      exact (hT t p p0).mpr (Or.inr (Or.inl ⟨h0, e1, rfl⟩))
  · intro t
    refine ⟨?_, ?_⟩
    · simp
    · intro p hp
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, (hT t p p).mpr (Or.inl rfl)⟩
