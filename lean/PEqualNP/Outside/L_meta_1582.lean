import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1582_aux

lemma inter_card_le_one {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 : Fin N} {T0 : Finset (Fin N)}
    (hint : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hsub : T0 ⊆ L i0) {t : Fin N} (ht : t ≠ i0) : (T0 ∩ L t).card ≤ 1 := by
  have hss : T0 ∩ L t ⊆ L i0 ∩ L t := by
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_inter]
    exact ⟨hsub hx.1, hx.2⟩
  calc (T0 ∩ L t).card ≤ (L i0 ∩ L t).card := Finset.card_le_card hss
    _ = (L t ∩ L i0).card := by rw [Finset.inter_comm]
    _ = 1 := hint t i0 ht

lemma filter_mem_card_le_one {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 : Fin N} {T0 : Finset (Fin N)}
    (hint : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hsub : T0 ⊆ L i0) {t : Fin N} (ht : t ≠ i0) :
    (T0.filter (fun x => x ∈ L t)).card ≤ 1 := by
  rw [Finset.filter_mem_eq_inter]
  exact inter_card_le_one hint hsub ht

lemma filter_not_card_ge {N : ℕ} {L : Fin N → Finset (Fin N)} {i0 : Fin N} {T0 : Finset (Fin N)} {m : ℕ}
    (hint : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hsub : T0 ⊆ L i0) (hT0 : T0.card = m) {t : Fin N} (ht : t ≠ i0) :
    m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card := by
  have h1 := filter_mem_card_le_one hint hsub ht
  have h2 := Finset.card_filter_add_card_filter_not (s := T0) (p := fun x => x ∈ L t)
  omega

end PEqualNP.Outside.L_meta_1582_aux

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
  intro q m N L i0 T0 hq hm hmq hN hcard hint hpair hsub hT0
  have hSplit : ∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card :=
    fun t ht => PEqualNP.Outside.L_meta_1582_aux.filter_not_card_ge hint hsub hT0 ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with ⟨v, hv, hxv⟩ | hx
    · exact Or.inl ⟨v, hv, hxy v hxv⟩
    · exact Or.inr (fun v hv => hxy v (hx v hv))
  · intro t
    by_cases ht : t = i0
    · rw [ht]
      exact Or.inr (fun v hv => decide_eq_true_iff.mpr hv)
    · left
      have hpos : 0 < (T0.filter (fun x => x ∉ L t)).card := by
        have h := hSplit t ht
        omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      have hv' := Finset.mem_filter.mp hv
      exact ⟨v, hv'.1, decide_eq_true_iff.mpr hv'.2⟩
  · intro t ht
    exact hSplit t ht
  · intro x hx
    exact Or.inl ⟨x, hx, decide_eq_true_iff.mpr rfl⟩
  · exact Or.inr (fun v hv => decide_eq_true_iff.mpr hv)
  · intro r hr
    exact Or.inr (fun v hv => decide_eq_true_iff.mpr (Or.inl hv))
  · intro t
    constructor
    · rw [decide_eq_false_iff_not]
      rintro ⟨v, hv, hd⟩
      exact (decide_eq_true_iff.mp hd) hv
    · intro p hp
      constructor
      · by_cases ht : t = i0
        · rw [ht]
          exact Or.inr (fun v hv => decide_eq_true_iff.mpr (Or.inl hv))
        · left
          have h2 : 2 ≤ (T0.filter (fun x => x ∉ L t)).card := by
            have h := hSplit t ht
            omega
          obtain ⟨v1, hv1, v2, hv2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < (T0.filter (fun x => x ∉ L t)).card)
          have hv1' := Finset.mem_filter.mp hv1
          have hv2' := Finset.mem_filter.mp hv2
          by_cases hp1 : v1 = p
          · exact ⟨v2, hv2'.1, decide_eq_true_iff.mpr (Or.inl hv2'.2)⟩
          · exact ⟨v1, hv1'.1, decide_eq_true_iff.mpr (Or.inl hv1'.2)⟩
      · rw [decide_eq_true_iff]
        exact ⟨p, hp, decide_eq_true_iff.mpr (Or.inr rfl)⟩
