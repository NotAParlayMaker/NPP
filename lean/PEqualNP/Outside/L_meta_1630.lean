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
  intro q N L i0 p0 p1 _ _ _ hint _ h01 h0 h1 T hT
  have key : ∀ t : Fin N, p0 ∈ L t → p1 ∈ L t → t = i0 := by
    intro t ht0 ht1
    by_contra hne
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hint t i0 hne)
    have e0 : p0 ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨ht0, h0⟩
    have e1 : p1 ∈ L t ∩ L i0 := Finset.mem_inter.mpr ⟨ht1, h1⟩
    rw [ha, Finset.mem_singleton] at e0 e1
    exact h01 (e0.trans e1.symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with h | h | h
    · exact Or.inl (hxy _ h)
    · exact Or.inr (Or.inl (hxy _ h))
    · exact Or.inr (Or.inr (fun u hu => hxy _ (h u hu)))
  · intro t
    by_cases ht0 : p0 ∈ L t
    · by_cases ht1 : p1 ∈ L t
      · have hti := key t ht0 ht1
        refine Or.inr (Or.inr ?_)
        intro u hu
        rw [← hti] at hu
        exact decide_eq_true hu
      · exact Or.inr (Or.inl (decide_eq_true ht1))
    · exact Or.inl (decide_eq_true ht0)
  · intro t p hp
    by_cases ht0 : p0 ∈ L t
    · by_cases ht1 : p1 ∈ L t
      · by_cases hp0 : p = p0
        · exact Or.inl ((hT t p p0).mpr (Or.inl hp0.symm))
        · by_cases hp1 : p = p1
          · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inl hp1.symm)))
          · refine Or.inr (Or.inr ?_)
            intro u hu
            have hti := key t ht0 ht1
            rw [← hti] at hu
            exact (hT t p u).mpr (Or.inr (Or.inr (Or.inr ⟨ht0, ht1, hp0, hp1, hu⟩)))
      · by_cases hp0 : p = p0
        · exact Or.inl ((hT t p p0).mpr (Or.inl hp0.symm))
        · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨ht0, ht1, hp0, rfl⟩)))))
    · by_cases hp1 : p = p1
      · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inl hp1.symm)))
      · exact Or.inl ((hT t p p0).mpr (Or.inr (Or.inl ⟨ht0, hp1, rfl⟩)))
  · intro t
    refine ⟨?_, ?_⟩
    · refine decide_eq_false ?_
      rintro ⟨v, hv, hv'⟩
      exact (of_decide_eq_true hv') hv
    · intro p hp
      exact decide_eq_true ⟨p, hp, (hT t p p).mpr (Or.inl rfl)⟩
