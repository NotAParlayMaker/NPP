import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1633

theorem ex {q N : ℕ} (L : Fin N → Finset (Fin N)) (hq : 3 ≤ q) (hc : ∀ i : Fin N, (L i).card = q + 1)
    (hi : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (t u : Fin N) (htu : t ≠ u) (x : Fin N) :
    ∃ p ∈ L t \ L u, p ≠ x := by
  have h1 : (L t \ L u).card + (L t ∩ L u).card = (L t).card := Finset.card_sdiff_add_card_inter (L t) (L u)
  rw [hc t, hi t u htu] at h1
  have h2 : (L t \ L u).card - 1 ≤ ((L t \ L u).erase x).card := Finset.pred_card_le_card_erase
  have h3 : 0 < ((L t \ L u).erase x).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp h3
  exact ⟨p, Finset.mem_of_mem_erase hp, Finset.ne_of_mem_erase hp⟩

theorem nb {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)
    (hi : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (h01 : p0 ≠ p1) (h0 : p0 ∈ L i0) (h1 : p1 ∈ L i0)
    (t : Fin N) (ht : t ≠ i0) : ¬ (p0 ∈ L t ∧ p1 ∈ L t) := by
  rintro ⟨a, b⟩
  have hsub : ({p0, p1} : Finset (Fin N)) ⊆ L t ∩ L i0 := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx]; exact Finset.mem_inter.mpr ⟨a, h0⟩
    · rw [hx]; exact Finset.mem_inter.mpr ⟨b, h1⟩
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_pair h01, hi t i0 ht] at h2
  omega

end PEqualNP.Outside.L_meta_1633

theorem PEqualNP.Outside.L_meta_1633 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ t u : Fin N, t ≠ i0 → u ≠ i0 → t ≠ u →
      ((∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ∧ (∃ p ∈ L u \ L t, ∃ v ∈ L t, T u p v = true) ↔ ((p0 ∈ L t ∧ p1 ∉ L t) ∧ (p1 ∈ L u ∧ p0 ∉ L u)) ∨ ((p1 ∈ L t ∧ p0 ∉ L t) ∧ (p0 ∈ L u ∧ p1 ∉ L u))) := by
  intro q N L i0 p0 p1 hq hN hc hi hj h01 h0 h1 T hT t u ht hu htu
  have A : ∀ t u : Fin N, t ≠ i0 → t ≠ u → ((∃ p ∈ L t \ L u, ∃ v ∈ L u, T t p v = true) ↔
      (p0 ∉ L t ∧ p0 ∈ L u) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p1 ∈ L u)) := by
    intro t u ht htu
    have nbt := PEqualNP.Outside.L_meta_1633.nb L i0 p0 p1 hi h01 h0 h1 t ht
    constructor
    · rintro ⟨p, hp, v, hv, hT'⟩
      rw [hT] at hT'
      rw [Finset.mem_sdiff] at hp
      rcases hT' with e | ⟨a, b, e⟩ | ⟨a, b, c, e⟩ | ⟨a, b, _⟩
      · rw [e] at hv
        exact absurd hv hp.2
      · rw [e] at hv
        exact Or.inl ⟨a, hv⟩
      · rw [e] at hv
        exact Or.inr ⟨a, b, hv⟩
      · exact absurd ⟨a, b⟩ nbt
    · rintro (⟨a, b⟩ | ⟨a, b, c⟩)
      · obtain ⟨p, hp, hp1⟩ := PEqualNP.Outside.L_meta_1633.ex L hq hc hi t u htu p1
        exact ⟨p, hp, p0, b, (hT t p p0).mpr (Or.inr (Or.inl ⟨a, hp1, rfl⟩))⟩
      · obtain ⟨p, hp, hp0⟩ := PEqualNP.Outside.L_meta_1633.ex L hq hc hi t u htu p0
        exact ⟨p, hp, p1, c, (hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨a, b, hp0, rfl⟩)))⟩
  refine (and_congr (A t u ht htu) (A u t hu (Ne.symm htu))).trans ?_
  tauto
