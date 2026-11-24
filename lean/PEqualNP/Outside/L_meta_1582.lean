import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1582 :
    ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N)
      (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 →
    (∀ i : Fin N, (L i).card = q + 1) →
    (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool,
        ((∃ v ∈ T0, x v = true) ∨
          ∀ v : Fin N, v ∉ L i0 → x v = true) →
        (∀ v : Fin N, x v = true → y v = true) →
        ((∃ v ∈ T0, y v = true) ∨
          ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N,
        ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨
          ∀ v : Fin N, v ∉ L i0 →
            (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧
    (∀ t : Fin N, t ≠ i0 →
        m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0,
        ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨
          ∀ v : Fin N, v ∉ L i0 →
            (fun v : Fin N => decide (v = x)) v = true)) ∧
    ((∃ v ∈ T0,
        (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨
      ∀ v : Fin N, v ∉ L i0 →
        (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧
    (∀ r ∈ L i0 \ T0,
        ((∃ v ∈ T0,
            (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨
          ∀ v : Fin N, v ∉ L i0 →
            (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N,
        decide (∃ v ∈ L t,
          (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
        ∀ p ∈ L t,
          ((∃ v ∈ T0,
              (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨
            ∀ v : Fin N, v ∉ L i0 →
              (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
          decide (∃ v ∈ L t,
              (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) := by
  classical
  intro q m N L i0 T0 hq hm hmq hN hsize hmeet hpairs hsubset hT0
  have hinter (t : Fin N) (ht : t ≠ i0) :
      (T0 ∩ L t).card ≤ 1 := by
    have hsub : T0 ∩ L t ⊆ L i0 ∩ L t := by
      intro v hv
      exact Finset.mem_inter.mpr
        ⟨hsubset (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
    calc
      (T0 ∩ L t).card ≤ (L i0 ∩ L t).card :=
        Finset.card_le_card hsub
      _ = 1 := hmeet i0 t (Ne.symm ht)
  have hfilter (t : Fin N) (ht : t ≠ i0) :
      m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card := by
    have hcard := Finset.card_sdiff_add_card_inter T0 (L t)
    have hdiff : T0.filter (fun x => x ∉ L t) = T0 \ L t := by
      ext x
      simp
    rw [hdiff]
    have hi := hinter t ht
    omega
  have hcol (t : Fin N) :
      (∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨
      ∀ v : Fin N, v ∉ L i0 →
        (fun v : Fin N => decide (v ∉ L t)) v = true := by
    by_cases ht : t = i0
    · subst t
      right
      intro v hv
      simp [hv]
    · left
      have hz : 0 < (T0.filter (fun x => x ∉ L t)).card := by
        have := hfilter t ht
        omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hz
      obtain ⟨hvmem, hvnot⟩ := Finset.mem_filter.mp hv
      exact ⟨v, hvmem, by simp [hvnot]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with ⟨v, hv, hxv⟩ | hall
    · exact Or.inl ⟨v, hv, hxy v hxv⟩
    · exact Or.inr (fun v hv => hxy v (hall v hv))
  · exact hcol
  · exact hfilter
  · intro x hx
    left
    exact ⟨x, hx, by simp⟩
  · right
    intro v hv
    simp [hv]
  · intro r hr
    right
    intro v hv
    simp [hv]
  · intro t
    constructor
    · simp
    · intro p hp
      constructor
      · by_cases ht : t = i0
        · subst t
          right
          intro v hv
          simp [hv]
        · left
          have hz : 0 < (T0.filter (fun x => x ∉ L t)).card := by
            have := hfilter t ht
            omega
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hz
          obtain ⟨hvmem, hvnot⟩ := Finset.mem_filter.mp hv
          exact ⟨v, hvmem, by simp [hvnot]⟩
      · simp only [decide_eq_true_eq]
        exact ⟨p, hp, Or.inr rfl⟩
