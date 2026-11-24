import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1540

theorem line_eq {N q : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)) (w : Fin N)
    (hL : ∀ i : Fin N, (L i).card = q + 1) (hT : T0 ⊆ L i0) (hTc : T0.card = q) (hw : w ∈ L i0)
    (hwT : w ∉ T0) : L i0 = insert w T0 := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    rcases Finset.mem_insert.mp hv with h | h
    · rw [h]; exact hw
    · exact hT h
  · rw [Finset.card_insert_eq_ite, if_neg hwT, hL, hTc]

theorem sub_eq {N q : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hq : 2 ≤ q) (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) (hT : T0 ⊆ L i0)
    (hTc : T0.card = q) (s : Fin N) (hs : T0 ⊆ L s) : s = i0 := by
  by_contra hne
  have h1 := hI s i0 hne
  have h2 : T0.card ≤ (L s ∩ L i0).card := Finset.card_le_card (Finset.subset_inter hs hT)
  omega

end PEqualNP.Outside.L_meta_1540

theorem PEqualNP.Outside.L_meta_1540 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)) (w : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = q → w ∈ L i0 → w ∉ T0 →
    (∀ x : Fin N → Bool, ((∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) ∧ ¬ ∃ v ∈ T0, x v = true) ↔
      (x = (fun v : Fin N => decide (v ∉ L i0)) ∨ x = (fun v : Fin N => decide (v ∉ L i0 ∨ v = w)))) ∧
    (∀ s : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L s)) v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, (fun v : Fin N => decide (v ∉ L s)) v = false → v ∈ L s) ∧ (s ≠ i0 → ∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L s)) v = true)) ∧
    (∀ x : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) ↔ ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true)) ∧
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, y v = false → v ∈ L s)) := by
  intro q N L i0 T0 w hq hN hL hI hP hT hTc hw hwT
  have hline := PEqualNP.Outside.L_meta_1540.line_eq L i0 T0 w hL hT hTc hw hwT
  have hsub := PEqualNP.Outside.L_meta_1540.sub_eq L i0 T0 hq hI hT hTc
  have key : ∀ x : Fin N → Bool, (∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) →
      (¬ ∃ v ∈ T0, x v = true) → ∀ v : Fin N, x v = false → v ∈ L i0 := by
    intro x hex hno
    obtain ⟨s, hs⟩ := hex
    have hsi : s = i0 := hsub s (fun v hv => hs v (by
      cases hx : x v with
      | false => rfl
      | true => exact absurd ⟨v, hv, hx⟩ hno))
    rw [hsi] at hs
    exact hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨hex, hno⟩
      have hk := key x hex hno
      have hT0 : ∀ v ∈ T0, x v = false := by
        intro v hv
        cases hx : x v with
        | false => rfl
        | true => exact absurd ⟨v, hv, hx⟩ hno
      have hoff : ∀ v : Fin N, v ∉ L i0 → x v = true := by
        intro v hv
        cases hx : x v with
        | false => exact absurd (hk v hx) hv
        | true => rfl
      cases hxw : x w with
      | false =>
        left
        funext v
        by_cases hv : v ∈ L i0
        · have hv' := hv
          rw [hline] at hv'
          rcases Finset.mem_insert.mp hv' with h | h
          · rw [h]; simp [hw, hxw]
          · simp [hv, hT0 v h]
        · simp [hv, hoff v hv]
      | true =>
        right
        funext v
        by_cases hvw : v = w
        · rw [hvw]; simp [hxw]
        · by_cases hv : v ∈ L i0
          · have hv' := hv
            rw [hline] at hv'
            rcases Finset.mem_insert.mp hv' with h | h
            · exact absurd h hvw
            · simp [hv, hvw, hT0 v h]
          · simp [hv, hoff v hv]
    · rintro (h | h)
      · rw [h]
        refine ⟨⟨i0, fun v hv => ?_⟩, ?_⟩
        · simpa using hv
        · rintro ⟨v, hv, hx⟩
          have h1 := hT hv
          simp [h1] at hx
      · rw [h]
        refine ⟨⟨i0, fun v hv => ?_⟩, ?_⟩
        · have h1 := hv
          simp at h1
          exact h1.1
        · rintro ⟨v, hv, hx⟩
          have h1 := hT hv
          have h2 : v ≠ w := fun h3 => hwT (h3 ▸ hv)
          simp [h1, h2] at hx
  · intro s
    refine ⟨Or.inr ⟨s, fun v hv => by simpa using hv⟩, fun hne => ?_⟩
    by_contra hcon
    apply hne
    apply hsub s
    intro v hv
    by_contra hvs
    exact hcon ⟨v, hv, by simp [hvs]⟩
  · intro x
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hno : ∃ v ∈ T0, x v = true
        · exact Or.inl hno
        · right
          intro v hv
          cases hx : x v with
          | false => exact absurd (key x h hno v hx) hv
          | true => rfl
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨i0, fun v hv => ?_⟩
        by_contra hvn
        have h1 := h v hvn
        rw [h1] at hv
        exact Bool.noConfusion hv
  · intro x y h hxy
    rcases h with ⟨v, hv, hx⟩ | ⟨s, hs⟩
    · exact Or.inl ⟨v, hv, hxy v hx⟩
    · refine Or.inr ⟨s, fun v hv => hs v ?_⟩
      cases hx : x v with
      | false => rfl
      | true =>
        have h1 := hxy v hx
        rw [h1] at hv
        exact Bool.noConfusion hv
