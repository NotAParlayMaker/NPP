import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1582

theorem main : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) := by
  intro q m N L i0 T0 _ hm _ _ _ hinter _ hTsub hTcard
  have hup : ∀ x y : Fin N → Bool,
      ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) →
      (∀ v : Fin N, x v = true → y v = true) →
      ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true) := by
    intro x y hx hxy
    rcases hx with ⟨v, hvT, hxv⟩ | hall
    · exact Or.inl ⟨v, hvT, hxy v hxv⟩
    · exact Or.inr (fun v hv => hxy v (hall v hv))
  have hfilter : ∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card := by
    intro t ht
    have hsub : T0.filter (fun x => x ∈ L t) ⊆ L i0 ∩ L t := by
      intro v hv
      obtain ⟨hvT, hvLt⟩ := Finset.mem_filter.1 hv
      exact Finset.mem_inter.2 ⟨hTsub hvT, hvLt⟩
    have hle1 : (T0.filter (fun x => x ∈ L t)).card ≤ 1 := by
      calc (T0.filter (fun x => x ∈ L t)).card
          ≤ (L i0 ∩ L t).card := Finset.card_le_card hsub
        _ = 1 := hinter i0 t (Ne.symm ht)
    have hsum := Finset.card_filter_add_card_filter_not (s := T0) (p := fun x => x ∈ L t)
    rw [hTcard] at hsum
    omega
  have hcoline : ∀ t : Fin N,
      ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨
        ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true) := by
    intro t
    by_cases ht : t = i0
    · subst ht
      exact Or.inr (fun v hv => decide_eq_true hv)
    · have hpos : 0 < (T0.filter (fun x => x ∉ L t)).card := by
        have := hfilter t ht
        omega
      obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
      obtain ⟨hvT, hvLt⟩ := Finset.mem_filter.1 hv
      exact Or.inl ⟨v, hvT, decide_eq_true hvLt⟩
  refine ⟨hup, hcoline, hfilter, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl ⟨x, hx, by simp⟩
  · exact Or.inr (fun v hv => decide_eq_true hv)
  · intro r _
    exact Or.inr (fun v hv => by simp [hv])
  · intro t
    refine ⟨by simp, ?_⟩
    intro p hp
    refine ⟨?_, ?_⟩
    · exact hup _ _ (hcoline t) (fun v hv => by simp [of_decide_eq_true hv])
    · exact decide_eq_true ⟨p, hp, by simp⟩

end PEqualNP.Outside.L_meta_1582

theorem PEqualNP.Outside.L_meta_1582 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) :=
  PEqualNP.Outside.L_meta_1582.main
