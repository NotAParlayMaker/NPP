import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside

theorem L_meta_473 :
    ∀ (V : Type) (G0 : SimpleGraph V) (N : ℕ) (num : V → ℕ) (G' : SimpleGraph (Fin N))
      (T0 : Finset V) (T1 : Finset (Fin N)),
      (∀ u v, G0.Adj u v → num u < N) →
      (∀ u v w z, G0.Adj u v → G0.Adj w z → num u = num w → u = w) →
      (∀ a b : Fin N, G'.Adj a b ↔ ∃ u v, G0.Adj u v ∧ num u = a.val ∧ num v = b.val) →
      (∀ u ∈ T0, ∃ v, G0.Adj u v) →
      (∀ a : Fin N, a ∈ T1 ↔ ∃ u ∈ T0, num u = a.val) →
      (∀ u v, G0.Adj u v → u ∈ T0 ∨ v ∈ T0) →
      (∀ a b, G'.Adj a b → a ∈ T1 ∨ b ∈ T1) ∧ T1.card = T0.card := by
  intro V G0 N num G' T0 T1 hlt hinj hG' hT0_edge hT1 hT0_cov
  constructor
  · intro a b hab
    rcases (hG' a b).mp hab with ⟨u, v, huv, hua, hvb⟩
    rcases hT0_cov u v huv with hu | hv
    · left
      exact (hT1 a).mpr ⟨u, hu, hua⟩
    · right
      exact (hT1 b).mpr ⟨v, hv, hvb⟩
  · symm
    refine Finset.card_bij
      (fun u (hu : u ∈ T0) =>
        (⟨num u, by
          rcases hT0_edge u hu with ⟨v, hv⟩
          exact hlt u v hv⟩ : Fin N)) ?_ ?_ ?_
    · intro u hu
      exact (hT1 _).mpr ⟨u, hu, rfl⟩
    · intro u1 hu1 u2 hu2 heq
      rcases hT0_edge u1 hu1 with ⟨v1, hv1⟩
      rcases hT0_edge u2 hu2 with ⟨v2, hv2⟩
      exact hinj u1 v1 u2 v2 hv1 hv2 (congrArg Fin.val heq)
    · intro a ha
      rcases (hT1 a).mp ha with ⟨u, hu, hua⟩
      exact ⟨u, hu, Fin.ext hua⟩

end PEqualNP.Outside
