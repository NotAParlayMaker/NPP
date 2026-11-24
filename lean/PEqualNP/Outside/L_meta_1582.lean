import Mathlib
import PEqualNP.Defs

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
  intro q m N L i0 T0 _ hm _ _ _ hInter _ hSubset hCard
  let inDomain (x : Fin N → Bool) : Prop :=
    (∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true
  have hUpward (x y : Fin N → Bool) (hx : inDomain x)
      (hxy : ∀ v, x v = true → y v = true) : inDomain y := by
    rcases hx with ⟨v, hv, hvTrue⟩ | hOutside
    · exact Or.inl ⟨v, hv, hxy v hvTrue⟩
    · exact Or.inr fun v hv => hxy v (hOutside v hv)
  have hCount (t : Fin N) (ht : t ≠ i0) :
      m - 1 ≤ (T0.filter (fun v => v ∉ L t)).card := by
    have hInside : (T0.filter (fun v => v ∈ L t)).card ≤ 1 := by
      rw [← hInter i0 t (Ne.symm ht)]
      apply Finset.card_le_card
      intro v hv
      obtain ⟨hvT0, hvt⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_inter.mpr ⟨hSubset hvT0, hvt⟩
    have hPartition := T0.card_filter_add_card_filter_not (fun v => v ∈ L t)
    omega
  have hColine (t : Fin N) : inDomain (fun v => decide (v ∉ L t)) := by
    by_cases ht : t = i0
    · subst t
      exact Or.inr fun v hv => decide_eq_true hv
    · have hOutside : 0 < (T0.filter (fun v => v ∉ L t)).card := by
        have := hCount t ht
        omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hOutside
      obtain ⟨hvT0, hvt⟩ := Finset.mem_filter.mp hv
      exact Or.inl ⟨v, hvT0, decide_eq_true hvt⟩
  have hAddPoint (t p : Fin N) : inDomain (fun v => decide (v ∉ L t ∨ v = p)) := by
    apply hUpward (fun v => decide (v ∉ L t)) _ (hColine t)
    intro v hv
    exact decide_eq_true (Or.inl (of_decide_eq_true hv))
  refine ⟨hUpward, hColine, hCount, ?_, hColine i0, ?_, ?_⟩
  · intro x hx
    exact Or.inl ⟨x, hx, decide_eq_true rfl⟩
  · intro r _
    exact hAddPoint i0 r
  · intro t
    constructor
    · apply decide_eq_false
      rintro ⟨v, hv, hvTrue⟩
      exact (of_decide_eq_true hvTrue) hv
    · intro p hp
      refine ⟨hAddPoint t p, decide_eq_true ?_⟩
      exact ⟨p, hp, decide_eq_true (Or.inr rfl)⟩
