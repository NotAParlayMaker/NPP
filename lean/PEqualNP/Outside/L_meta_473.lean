import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_473 :
    ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N))
      (T0 : Finset V) (T1 : Finset (Fin N)),
      (∀ u v, G0.Adj u v → num u < N) →
      (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) →
      (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) →
      (∀ u ∈ T0, ∃ v, G0.Adj u v) →
      (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) →
      (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) →
      (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card := by
  intro V G0 N num G' T0 T1 hN hinj hG' hnb hT1 hcov
  have hcover : ∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1 := by
    intro a b hab
    obtain ⟨u, v, huv, hu, hv⟩ := (hG' a b).1 hab
    rcases hcov u v huv with h | h
    · exact Or.inl ((hT1 a).2 ⟨u, h, hu⟩)
    · exact Or.inr ((hT1 b).2 ⟨v, h, hv⟩)
  refine ⟨hcover, ?_⟩
  by_cases hN0 : N = 0
  · subst hN0
    have hT0 : T0 = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨u, hu⟩
      obtain ⟨v, hv⟩ := hnb u hu
      have h := hN u v hv
      omega
    have hT1' : T1 = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨a, -⟩
      exact Fin.elim0 a
    rw [hT0, hT1']
    simp
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
    let f : V → Fin N := fun u => if h : num u < N then ⟨num u, h⟩ else ⟨0, hNpos⟩
    have hlt : ∀ u ∈ T0, num u < N := by
      intro u hu
      obtain ⟨v, hv⟩ := hnb u hu
      exact hN u v hv
    have hfv : ∀ u ∈ T0, (f u).val = num u := by
      intro u hu
      have hltu : num u < N := hlt u hu
      show (if h : num u < N then (⟨num u, h⟩ : Fin N) else (⟨0, hNpos⟩ : Fin N)).val = num u
      rw [dif_pos hltu]
    have hinjf : Set.InjOn f ↑T0 := by
      intro u hu w hw heq
      have hval : num u = num w := by
        rw [← hfv u hu, ← hfv w hw, heq]
      obtain ⟨v, hv⟩ := hnb u hu
      obtain ⟨z, hz⟩ := hnb w hw
      exact hinj u v w z hv hz hval
    have hsurj : ∀ a ∈ T1, ∃ u ∈ T0, f u = a := by
      intro a ha
      obtain ⟨u, hu, hnum⟩ := (hT1 a).1 ha
      refine ⟨u, hu, ?_⟩
      apply Fin.ext
      rw [hfv u hu, hnum]
    have heq : T1 = T0.image f := by
      refine Finset.ext fun a => ?_
      constructor
      · intro ha
        obtain ⟨u, hu, hfu⟩ := hsurj a ha
        exact Finset.mem_image.2 ⟨u, hu, hfu⟩
      · intro ha
        obtain ⟨u, hu, hfu⟩ := Finset.mem_image.1 ha
        rw [← hfu]
        exact (hT1 (f u)).2 ⟨u, hu, (hfv u hu).symm⟩
    rw [heq]
    exact Finset.card_image_of_injOn hinjf
