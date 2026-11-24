import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L1582

theorem key {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 t : Fin N) (T0 : Finset (Fin N))
    (hint : (L t ∩ L i0).card = 1) (hT : T0 ⊆ L i0) :
    T0.card - 1 ≤ (T0.filter (fun x => x ∉ L t)).card := by
  have h1 : (T0.filter (fun x => x ∈ L t)).card ≤ 1 := by
    calc (T0.filter (fun x => x ∈ L t)).card ≤ (L t ∩ L i0).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx
          exact Finset.mem_inter.mpr ⟨hx.2, hT hx.1⟩
      _ = 1 := hint
  have h2 := Finset.card_filter_add_card_filter_not (s := T0) (fun x => x ∈ L t)
  omega

theorem off_line {N m : ℕ} (L : Fin N → Finset (Fin N)) (i0 t : Fin N) (T0 : Finset (Fin N))
    (hm : 3 ≤ m) (hT0 : T0.card = m) (hint : (L t ∩ L i0).card = 1) (hT : T0 ⊆ L i0) :
    ∃ v ∈ T0, v ∉ L t := by
  have h := key L i0 t T0 hint hT
  have hpos : 0 < (T0.filter (fun x => x ∉ L t)).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hv
  exact ⟨v, hv.1, hv.2⟩

end PEqualNP.Outside.L1582

theorem PEqualNP.Outside.L_meta_1582 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) := by
  intro q m N L i0 T0 hq hm hmq hN hcard hint hcov hT hT0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with ⟨v, hv, hxv⟩ | hall
    · exact Or.inl ⟨v, hv, hxy v hxv⟩
    · exact Or.inr (fun v hv => hxy v (hall v hv))
  · intro t
    by_cases ht : t = i0
    · subst ht
      right
      intro v hv
      simpa using hv
    · obtain ⟨v, hv, hvt⟩ := PEqualNP.Outside.L1582.off_line L i0 t T0 hm hT0 (hint t i0 ht) hT
      left
      exact ⟨v, hv, by simpa using hvt⟩
  · intro t ht
    have h := PEqualNP.Outside.L1582.key L i0 t T0 (hint t i0 ht) hT
    rw [hT0] at h
    exact h
  · intro x hx
    left
    exact ⟨x, hx, by simp⟩
  · right
    intro v hv
    simpa using hv
  · intro r hr
    right
    intro v hv
    simp [hv]
  · intro t
    refine ⟨by simp, ?_⟩
    intro p hp
    refine ⟨?_, ?_⟩
    · by_cases ht : t = i0
      · subst ht
        right
        intro v hv
        simp [hv]
      · obtain ⟨v, hv, hvt⟩ := PEqualNP.Outside.L1582.off_line L i0 t T0 hm hT0 (hint t i0 ht) hT
        left
        exact ⟨v, hv, by simp [hvt]⟩
    · exact decide_eq_true ⟨p, hp, by simp⟩
