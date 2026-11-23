import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_473 : ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N)) (T0 : Finset V) (T1 : Finset (Fin N)), (∀ u v, G0.Adj u v → num u < N) → (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) → (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) → (∀ u ∈ T0, ∃ v, G0.Adj u v) → (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) → (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) → (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card := by
  classical
  intro V G0 N num G' T0 T1 hbound hinj hG hinc hT hcover
  constructor
  · intro a b hab
    obtain ⟨u, v, huv, hua, hvb⟩ := (hG a b).mp hab
    rcases hcover u v huv with hu | hv
    · exact Or.inl ((hT a).mpr ⟨u, hu, hua⟩)
    · exact Or.inr ((hT b).mpr ⟨v, hv, hvb⟩)
  · symm
    apply Finset.card_bij (fun u hu =>
      (⟨num u, by
        obtain ⟨v, huv⟩ := hinc u hu
        exact hbound u v huv⟩ : Fin N))
    · intro u hu
      exact (hT _).mpr ⟨u, hu, rfl⟩
    · intro u hu w hw heq
      obtain ⟨v, huv⟩ := hinc u hu
      obtain ⟨z, hwz⟩ := hinc w hw
      exact hinj u v w z huv hwz (congrArg (fun a : Fin N => a.val) heq)
    · intro a ha
      obtain ⟨u, hu, hnum⟩ := (hT a).mp ha
      exact ⟨u, hu, Fin.ext hnum⟩
