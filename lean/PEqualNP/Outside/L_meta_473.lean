import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_473 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)) (T0 : Finset V) (T1 : Finset (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → (∀ u ∈ T0, ∃ v, G0.Adj u v) → (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) → (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) → (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card := by
  intro V G0 N num G' T0 T1 h1 h2 h3 h4 h5 h6
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨u, v, huv, hu, hv⟩ := (h3 a b).1 hab
    rcases h6 u v huv with h | h
    · exact Or.inl ((h5 a).2 ⟨u, h, hu⟩)
    · exact Or.inr ((h5 b).2 ⟨v, h, hv⟩)
  · symm
    refine Finset.card_bij (fun u hu => (⟨num u, h1 u _ (h4 u hu).choose_spec⟩ : Fin N)) ?_ ?_ ?_
    · intro u hu
      exact (h5 _).2 ⟨u, hu, rfl⟩
    · intro u hu w hw huw
      have e : num u = num w := congrArg Fin.val huw
      exact h2 u _ w _ (h4 u hu).choose_spec (h4 w hw).choose_spec e
    · intro b hb
      obtain ⟨u, hu, hub⟩ := (h5 b).1 hb
      exact ⟨u, hu, Fin.ext hub⟩
