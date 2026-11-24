import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1630

theorem line_eq {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (h2 : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hne : p0 ≠ p1) (h0 : p0 ∈ L i0) (h1 : p1 ∈ L i0)
    (t : Fin N) (a0 : p0 ∈ L t) (a1 : p1 ∈ L t) : t = i0 := by
  by_contra hti
  have hc := h2 t i0 hti
  have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_inter.mpr ⟨a0, h0⟩
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_inter.mpr ⟨a1, h1⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hne, hc] at hle
  omega

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
    (∀ t : Fin N, decide (∃ v ∈ L t, decide (v ∉ L t) = true) = false ∧ ∀ p ∈ L t, decide (∃ v ∈ L t, T t p v = true) = true) := by
  intro q N L i0 p0 p1 _ _ _ h2 _ hne h0 h1 T hT
  have key := PEqualNP.Outside.L_meta_1630.line_eq L i0 p0 p1 h2 hne h0 h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with hx | hx | hx
    · exact Or.inl (hxy _ hx)
    · exact Or.inr (Or.inl (hxy _ hx))
    · exact Or.inr (Or.inr (fun u hu => hxy _ (hx u hu)))
  · intro t
    by_cases a0 : p0 ∈ L t
    · by_cases a1 : p1 ∈ L t
      · have ht := key t a0 a1
        subst ht
        refine Or.inr (Or.inr ?_)
        intro u hu
        exact decide_eq_true hu
      · exact Or.inr (Or.inl (decide_eq_true a1))
    · exact Or.inl (decide_eq_true a0)
  · intro t p _
    by_cases e0 : p = p0
    · exact Or.inl ((hT t p p0).mpr (Or.inl e0.symm))
    by_cases e1 : p = p1
    · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inl e1.symm)))
    by_cases a0 : p0 ∈ L t
    · by_cases a1 : p1 ∈ L t
      · have ht := key t a0 a1
        subst ht
        refine Or.inr (Or.inr ?_)
        intro u hu
        exact (hT t p u).mpr (Or.inr (Or.inr (Or.inr ⟨a0, a1, e0, e1, hu⟩)))
      · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨a0, a1, e0, rfl⟩)))))
    · exact Or.inl ((hT t p p0).mpr (Or.inr (Or.inl ⟨a0, e1, rfl⟩)))
  · intro t
    refine ⟨?_, ?_⟩
    · apply decide_eq_false
      rintro ⟨v, hv, hd⟩
      exact (of_decide_eq_true hd) hv
    · intro p hp
      apply decide_eq_true
      exact ⟨p, hp, (hT t p p).mpr (Or.inl rfl)⟩
