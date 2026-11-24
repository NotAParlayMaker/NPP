import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1630

theorem main : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
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
  intro q N L i0 p0 p1 _ _ _ hinter _ hp01 hp0 hp1 T hT
  have huniq : ∀ t : Fin N, p0 ∈ L t → p1 ∈ L t → t = i0 := by
    intro t ht0 ht1
    by_contra hne
    have h1 := hinter t i0 hne
    have heq := Finset.card_le_one.1 (le_of_eq h1) p0 (Finset.mem_inter.2 ⟨ht0, hp0⟩)
      p1 (Finset.mem_inter.2 ⟨ht1, hp1⟩)
    exact hp01 heq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with h0 | h1 | hall
    · exact Or.inl (hxy p0 h0)
    · exact Or.inr (Or.inl (hxy p1 h1))
    · exact Or.inr (Or.inr (fun u hu => hxy u (hall u hu)))
  · intro t
    by_cases ht0 : p0 ∈ L t
    · by_cases ht1 : p1 ∈ L t
      · have hti : t = i0 := huniq t ht0 ht1
        subst hti
        exact Or.inr (Or.inr (fun u hu => decide_eq_true hu))
      · exact Or.inr (Or.inl (decide_eq_true ht1))
    · exact Or.inl (decide_eq_true ht0)
  · intro t p _
    by_cases hpp0 : p = p0
    · exact Or.inl ((hT t p p0).2 (Or.inl hpp0.symm))
    · by_cases hpp1 : p = p1
      · exact Or.inr (Or.inl ((hT t p p1).2 (Or.inl hpp1.symm)))
      · by_cases ht0 : p0 ∈ L t
        · by_cases ht1 : p1 ∈ L t
          · have hti : t = i0 := huniq t ht0 ht1
            subst hti
            exact Or.inr (Or.inr (fun u hu => (hT t p u).2 (Or.inr (Or.inr (Or.inr ⟨ht0, ht1, hpp0, hpp1, hu⟩)))))
          · exact Or.inr (Or.inl ((hT t p p1).2 (Or.inr (Or.inr (Or.inl ⟨ht0, ht1, hpp0, rfl⟩)))))
        · exact Or.inl ((hT t p p0).2 (Or.inr (Or.inl ⟨ht0, hpp1, rfl⟩)))
  · intro t
    refine ⟨by simp, ?_⟩
    intro p hp
    exact decide_eq_true ⟨p, hp, (hT t p p).2 (Or.inl rfl)⟩

end PEqualNP.Outside.L_meta_1630

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
    (∀ t : Fin N, decide (∃ v ∈ L t, decide (v ∉ L t) = true) = false ∧ ∀ p ∈ L t, decide (∃ v ∈ L t, T t p v = true) = true) :=
  PEqualNP.Outside.L_meta_1630.main
