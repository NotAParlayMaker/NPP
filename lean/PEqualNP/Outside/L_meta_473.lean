import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_473 :
    ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)) (T0 : Finset V) (T1 : Finset (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → (∀ u ∈ T0, ∃ v, G0.Adj u v) → (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) → (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) → (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card := by
  intro V G0 N num G' T0 T1 hN hinj hG' hT0 hT1 hcov
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨u, v, huv, hua, hvb⟩ := (hG' a b).1 hab
    rcases hcov u v huv with hu | hv
    · exact Or.inl ((hT1 a).2 ⟨u, hu, hua⟩)
    · exact Or.inr ((hT1 b).2 ⟨v, hv, hvb⟩)
  · symm
    refine Finset.card_bij
      (fun u hu => (⟨num u, hN u (hT0 u hu).choose (hT0 u hu).choose_spec⟩ : Fin N)) ?_ ?_ ?_
    · intro u hu
      exact (hT1 _).2 ⟨u, hu, rfl⟩
    · intro u hu w hw h
      have h' : num u = num w := congrArg Fin.val h
      exact hinj u _ w _ (hT0 u hu).choose_spec (hT0 w hw).choose_spec h'
    · intro a ha
      obtain ⟨u, hu, hua⟩ := (hT1 a).1 ha
      exact ⟨u, hu, Fin.ext hua⟩
