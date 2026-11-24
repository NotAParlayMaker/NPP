import Mathlib.Data.Finset.Card

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
  intro q m N L i0 T0 hq hm hmq hN hcard hinter hjoin hsub hT
  have hdiff (t : Fin N) (ht : t ≠ i0) :
      m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card := by
    have hs : T0 ∩ L t ⊆ L i0 ∩ L t := by
      intro x hx
      rw [Finset.mem_inter] at hx ⊢
      exact ⟨hsub hx.1, hx.2⟩
    have hb := Finset.card_le_card hs
    rw [hinter i0 t (Ne.symm ht)] at hb
    have he := Finset.card_sdiff_add_card_inter T0 (L t)
    have hf : T0.filter (fun x => x ∉ L t) = T0 \ L t := by
      ext x
      simp
    rw [hf, hT] at *
    omega
  have hout (t : Fin N) (ht : t ≠ i0) : ∃ v ∈ T0, v ∉ L t := by
    have hc := hdiff t ht
    have hp : 0 < (T0.filter (fun x => x ∉ L t)).card := by omega
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hp
    exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  refine ⟨?_, ?_, hdiff, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with ⟨v,hv,hx⟩ | hx
    · exact Or.inl ⟨v,hv,hxy v hx⟩
    · exact Or.inr (fun v hv => hxy v (hx v hv))
  · intro t
    by_cases ht : t = i0
    · subst t
      exact Or.inr (fun v hv => by simpa using hv)
    · obtain ⟨v,hv,hn⟩ := hout t ht
      exact Or.inl ⟨v,hv,by simpa using hn⟩
  · intro x hx
    exact Or.inl ⟨x,hx,by simp⟩
  · exact Or.inr (fun v hv => by simpa using hv)
  · intro r hr
    exact Or.inr (fun v hv => by simp [hv])
  · intro t
    constructor
    · simp
    · intro p hp
      constructor
      · by_cases ht : t = i0
        · subst t
          exact Or.inr (fun v hv => by simp [hv])
        · obtain ⟨v,hv,hn⟩ := hout t ht
          exact Or.inl ⟨v,hv,by simp [hn]⟩
      · simp only [decide_eq_true_eq]
        exact ⟨p,hp,by simp⟩
