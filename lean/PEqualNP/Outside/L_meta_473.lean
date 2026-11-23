import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_473 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)) (T0 : Finset V) (T1 : Finset (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → (∀ u ∈ T0, ∃ v, G0.Adj u v) → (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) → (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) → (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card := by
  classical
  intro V G₀ N num G' T₀ T₁ hbound hinj hedge hincident hmem hcover
  constructor
  · intro a b hab
    obtain ⟨u, v, huv, hua, hvb⟩ := (hedge a b).mp hab
    rcases hcover u v huv with hu | hv
    · exact Or.inl ((hmem a).mpr ⟨u, hu, hua⟩)
    · exact Or.inr ((hmem b).mpr ⟨v, hv, hvb⟩)
  · have hlt (u : V) (hu : u ∈ T₀) : num u < N := by
      obtain ⟨v, huv⟩ := hincident u hu
      exact hbound u v huv
    symm
    refine Finset.card_bij (fun u hu => (⟨num u, hlt u hu⟩ : Fin N)) ?_ ?_ ?_
    · intro u hu
      exact (hmem _).mpr ⟨u, hu, rfl⟩
    · intro u hu w hw he
      obtain ⟨v, huv⟩ := hincident u hu
      obtain ⟨z, hwz⟩ := hincident w hw
      exact hinj u v w z huv hwz (congrArg Fin.val he)
    · intro a ha
      obtain ⟨u, hu, he⟩ := (hmem a).mp ha
      exact ⟨u, hu, Fin.ext he⟩
