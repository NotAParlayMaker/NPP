import Mathlib

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
  classical
  intro q m N L i0 T0 hq hm hmq hN hcard hinter hpoints hsub hT
  let D : (Fin N → Bool) → Prop := fun x =>
    (∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true
  have hup : ∀ x y : Fin N → Bool, D x → (∀ v, x v = true → y v = true) → D y := by
    intro x y hx hxy
    rcases hx with ⟨v, hv, hxv⟩ | hx
    · exact Or.inl ⟨v, hv, hxy v hxv⟩
    · exact Or.inr fun v hv => hxy v (hx v hv)
  have hcount : ∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter fun x => x ∉ L t).card := by
    intro t ht
    have hsi : T0 ∩ L t ⊆ L i0 ∩ L t := by
      intro x hx
      obtain ⟨hxT, hxt⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hsub hxT, hxt⟩
    have hle := Finset.card_le_card hsi
    rw [hinter i0 t (Ne.symm ht)] at hle
    have he : T0 \ L t = T0.filter (fun x => x ∉ L t) := by ext x; simp
    have hp := Finset.card_sdiff_add_card_inter T0 (L t)
    rw [he, hT] at hp
    omega
  have hco : ∀ t : Fin N, D (fun v => decide (v ∉ L t)) := by
    intro t
    by_cases ht : t = i0
    · subst t
      exact Or.inr fun v hv => by simpa using hv
    · have hc := hcount t ht
      have hp : 0 < (T0.filter fun x => x ∉ L t).card := by omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hp
      obtain ⟨hvT, hvt⟩ := Finset.mem_filter.mp hv
      exact Or.inl ⟨v, hvT, by simpa using hvt⟩
  refine ⟨hup, hco, hcount, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Or.inl ⟨x, hx, by simp⟩
  · exact Or.inr fun v hv => by simpa using hv
  · intro r hr
    exact Or.inr fun v hv => by simp [hv]
  · intro t
    constructor
    · simp
    · intro p hp
      constructor
      · apply hup (fun v => decide (v ∉ L t)) _ (hco t)
        intro v hv
        have hvt : v ∉ L t := by simpa using hv
        simp [hvt]
      · simp only [decide_eq_true_eq]
        exact ⟨p, hp, by simp⟩
