import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1540

theorem line_eq {q N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N))
    (hq : 2 ≤ q) (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hT : T0 ⊆ L i0) (hc : T0.card = q) (s : Fin N) (hs : T0 ⊆ L s) : s = i0 := by
  by_contra hne
  have h1 := hI s i0 hne
  have h2 : T0.card ≤ (L s ∩ L i0).card :=
    Finset.card_le_card (Finset.subset_inter hs hT)
  omega

theorem line_split {q N : ℕ} (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)) (w : Fin N)
    (hL : (L i0).card = q + 1)
    (hT : T0 ⊆ L i0) (hc : T0.card = q) (hw : w ∈ L i0) (hwT : w ∉ T0) (v : Fin N) (hv : v ∈ L i0) :
    v ∈ T0 ∨ v = w := by
  have hsub : insert w T0 ⊆ L i0 := Finset.insert_subset hw hT
  have hcard : (insert w T0).card = q + 1 := by rw [Finset.card_insert_of_notMem hwT, hc]
  have heq : insert w T0 = L i0 := Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [← heq] at hv
  rcases Finset.mem_insert.mp hv with h | h
  · exact Or.inr h
  · exact Or.inl h

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
  intro q N L i0 T0 w hq _ hL hI _ hT hc hw hwT
  have H := PEqualNP.Outside.L_meta_1540.line_eq L i0 T0 hq hI hT hc
  have S := PEqualNP.Outside.L_meta_1540.line_split L i0 T0 w (hL i0) hT hc hw hwT
  have H3 : ∀ x : Fin N → Bool, (∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) →
      ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) := by
    intro x ⟨s, hs⟩
    by_cases hex : ∃ v ∈ T0, x v = true
    · exact Or.inl hex
    · right
      have hTs : T0 ⊆ L s := by
        intro v hv
        apply hs
        by_contra hx
        exact hex ⟨v, hv, by simpa using hx⟩
      have := H s hTs
      subst this
      intro v hv
      by_contra hx
      exact hv (hs v (by simpa using hx))
  have H3' : ∀ x : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) →
      ((∃ v ∈ T0, x v = true) ∨ ∃ s : Fin N, ∀ v : Fin N, x v = false → v ∈ L s) := by
    intro x h
    rcases h with h | h
    · exact Or.inl h
    · right
      refine ⟨i0, fun v hx => ?_⟩
      by_contra hv
      rw [h v hv] at hx
      exact Bool.noConfusion hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨hs, hex⟩
      have h3 := (H3 x hs).resolve_left hex
      have hT0 : ∀ v ∈ T0, x v = false := by
        intro v hv
        by_contra hx
        exact hex ⟨v, hv, by simpa using hx⟩
      by_cases hxw : x w = true
      · right
        funext v
        by_cases hv : v ∈ L i0
        · rcases S v hv with h | h
          · have : v ≠ w := fun e => hwT (e ▸ h)
            simp [hT0 v h, hv, this]
          · subst h
            simp [hxw]
        · simp [h3 v hv, hv]
      · left
        funext v
        by_cases hv : v ∈ L i0
        · rcases S v hv with h | h
          · simp [hT0 v h, hv]
          · subst h
            simp [hv]
            simpa using hxw
        · simp [h3 v hv, hv]
    · intro h
      rcases h with h | h
      · subst h
        refine ⟨⟨i0, fun v hv => by simpa using hv⟩, ?_⟩
        rintro ⟨v, hv, hx⟩
        simp [hT hv] at hx
      · subst h
        refine ⟨⟨i0, fun v hv => ?_⟩, ?_⟩
        · by_contra hn
          simp [hn] at hv
        · rintro ⟨v, hv, hx⟩
          have : v ≠ w := fun e => hwT (e ▸ hv)
          simp [hT hv, this] at hx
  · intro s
    have key : s ≠ i0 → ∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L s)) v = true := by
      intro hne
      by_contra hex
      apply hne
      apply H
      intro v hv
      by_contra hn
      exact hex ⟨v, hv, by simpa using hn⟩
    refine ⟨?_, key⟩
    by_cases hs : s = i0
    · right
      refine ⟨s, fun v hv => ?_⟩
      by_contra hn
      simp [hn] at hv
    · exact Or.inl (key hs)
  · intro x
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · exact H3 x h
    · exact H3' x
  · intro x y h hxy
    rcases h with ⟨v, hv, hx⟩ | ⟨s, hs⟩
    · exact Or.inl ⟨v, hv, hxy v hx⟩
    · right
      refine ⟨s, fun v hy => hs v ?_⟩
      by_contra hx
      have := hxy v (by simpa using hx)
      rw [this] at hy
      exact Bool.noConfusion hy
