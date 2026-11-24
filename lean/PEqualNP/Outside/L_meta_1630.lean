import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1630_aux

lemma eq_i0_of_mem {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 p0 p1 : Fin N}
    (hinter : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0) (hp01 : p0 ≠ p1) {t : Fin N}
    (h0 : p0 ∈ L t) (h1 : p1 ∈ L t) : t = i0 := by
  by_contra hne
  have hc := hinter i0 t (Ne.symm hne)
  have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L i0 ∩ L t := by
    intro x hx
    rw [Finset.mem_inter]
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨hp0, h0⟩
    · exact ⟨hp1, h1⟩
  have h2 : ({p0, p1} : Finset (Fin N)).card = 2 := Finset.card_pair hp01
  have hle := Finset.card_le_card hsub
  omega

end PEqualNP.Outside.L_meta_1630_aux

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
  intro q N L i0 p0 p1 hq hN hcard hinter hcover hp01 hp0 hp1 T hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with h | h | h
    · exact Or.inl (hxy _ h)
    · exact Or.inr (Or.inl (hxy _ h))
    · exact Or.inr (Or.inr (fun u hu => hxy _ (h u hu)))
  · intro t
    by_cases h0 : p0 ∈ L t
    · by_cases h1 : p1 ∈ L t
      · have ht : t = i0 := PEqualNP.Outside.L_meta_1630_aux.eq_i0_of_mem hinter hp0 hp1 hp01 h0 h1
        refine Or.inr (Or.inr (fun u hu => ?_))
        rw [ht]
        exact decide_eq_true_iff.mpr hu
      · exact Or.inr (Or.inl (decide_eq_true_iff.mpr h1))
    · exact Or.inl (decide_eq_true_iff.mpr h0)
  · intro t p hp
    by_cases hpp0 : p = p0
    · exact Or.inl ((hT t p p0).mpr (Or.inl hpp0.symm))
    · by_cases hpp1 : p = p1
      · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inl hpp1.symm)))
      · by_cases h0 : p0 ∈ L t
        · by_cases h1 : p1 ∈ L t
          · have ht : t = i0 := PEqualNP.Outside.L_meta_1630_aux.eq_i0_of_mem hinter hp0 hp1 hp01 h0 h1
            refine Or.inr (Or.inr (fun u hu => ?_))
            have hu' : u ∉ L t := by rw [ht]; exact hu
            exact (hT t p u).mpr (Or.inr (Or.inr (Or.inr ⟨h0, h1, hpp0, hpp1, hu'⟩)))
          · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨h0, h1, hpp0, rfl⟩)))))
        · exact Or.inl ((hT t p p0).mpr (Or.inr (Or.inl ⟨h0, hpp1, rfl⟩)))
  · intro t
    refine ⟨?_, ?_⟩
    · refine decide_eq_false_iff_not.mpr ?_
      rintro ⟨v, hv, hdv⟩
      exact (decide_eq_true_iff.mp hdv) hv
    · intro p hp
      exact decide_eq_true_iff.mpr ⟨p, hp, (hT t p p).mpr (Or.inl rfl)⟩
