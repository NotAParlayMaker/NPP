import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_473 :
    ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)) (T0 : Finset V) (T1 : Finset (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → (∀ u ∈ T0, ∃ v, G0.Adj u v) → (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) → (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) → (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card := by
  intro V G0 N num G' T0 T1 hbound hinj hadj hT0_edge hT1_mem hcover
  constructor
  · intro a b hab
    obtain ⟨u, v, huv, hu, hv⟩ := (hadj a b).mp hab
    rcases hcover u v huv with huT | hvT
    · exact Or.inl ((hT1_mem a).mpr ⟨u, huT, hu⟩)
    · exact Or.inr ((hT1_mem b).mpr ⟨v, hvT, hv⟩)
  · symm
    refine Finset.card_bij
      (fun u (hu : u ∈ T0) => (⟨num u, by obtain ⟨v, hv⟩ := hT0_edge u hu; exact hbound u v hv⟩ : Fin N))
      ?_ ?_ ?_
    · intro u hu
      exact (hT1_mem _).mpr ⟨u, hu, rfl⟩
    · intro u₁ hu₁ u₂ hu₂ hEq
      obtain ⟨v₁, hv₁⟩ := hT0_edge u₁ hu₁
      obtain ⟨v₂, hv₂⟩ := hT0_edge u₂ hu₂
      exact hinj u₁ v₁ u₂ v₂ hv₁ hv₂ (congrArg Fin.val hEq)
    · intro a ha
      obtain ⟨u, hu, hnum⟩ := (hT1_mem a).mp ha
      exact ⟨u, hu, Fin.ext hnum⟩
