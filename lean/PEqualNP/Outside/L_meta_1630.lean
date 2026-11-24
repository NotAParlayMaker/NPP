import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1630

theorem line_of_both {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 t : Fin N)
    (hL : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (h01 : p0 ≠ p1) (h0 : p0 ∈ L i0) (h1 : p1 ∈ L i0)
    (ht0 : p0 ∈ L t) (ht1 : p1 ∈ L t) : t = i0 := by
  by_contra hne
  have hc := hL t i0 hne
  have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · rw [hv]
      exact Finset.mem_inter.mpr ⟨ht0, h0⟩
    · rw [hv]
      exact Finset.mem_inter.mpr ⟨ht1, h1⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair h01, hc] at hle
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
  intro q N L i0 p0 p1 _ _ _ hL _ h01 h0 h1 T hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with h | h | h
    · exact Or.inl (hxy _ h)
    · exact Or.inr (Or.inl (hxy _ h))
    · exact Or.inr (Or.inr fun u hu => hxy _ (h u hu))
  · intro t
    by_cases ht : t = i0
    · refine Or.inr (Or.inr fun u hu => ?_)
      rw [ht]
      simpa using hu
    · by_cases ht0 : p0 ∈ L t
      · by_cases ht1 : p1 ∈ L t
        · exact absurd
            (PEqualNP.Outside.L_meta_1630.line_of_both L i0 p0 p1 t hL h01 h0 h1 ht0 ht1) ht
        · exact Or.inr (Or.inl (by simpa using ht1))
      · exact Or.inl (by simpa using ht0)
  · intro t p hp
    by_cases hp0 : p = p0
    · exact Or.inl ((hT t p p0).mpr (Or.inl hp0.symm))
    by_cases hp1 : p = p1
    · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inl hp1.symm)))
    by_cases ht0 : p0 ∈ L t
    · by_cases ht1 : p1 ∈ L t
      · have hti :=
          PEqualNP.Outside.L_meta_1630.line_of_both L i0 p0 p1 t hL h01 h0 h1 ht0 ht1
        refine Or.inr (Or.inr fun u hu => ?_)
        have hut : u ∉ L t := by
          rw [hti]
          exact hu
        exact (hT t p u).mpr (Or.inr (Or.inr (Or.inr ⟨ht0, ht1, hp0, hp1, hut⟩)))
      · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨ht0, ht1, hp0, rfl⟩)))))
    · exact Or.inl ((hT t p p0).mpr (Or.inr (Or.inl ⟨ht0, hp1, rfl⟩)))
  · intro t
    refine ⟨?_, fun p hp => ?_⟩
    · simp
    · simp only [decide_eq_true_eq]
      exact ⟨p, hp, (hT t p p).mpr (Or.inl rfl)⟩
