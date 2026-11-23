import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace PEqualNP.Outside

theorem L_meta_253 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (x : Fin n → Bool),
      decide (∃ u w : Fin n, G.Adj u w ∧ Function.update x v false u = true ∧ Function.update x v false w = true) =
      decide (∃ u w : Fin n, u ≠ v ∧ w ≠ v ∧ G.Adj u w ∧ x u = true ∧ x w = true) := by
  intro n G _ v x
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨u, w, hadj, hu, hw⟩
    have huv : u ≠ v := by
      intro h
      subst h
      simp at hu
    have hwv : w ≠ v := by
      intro h
      subst h
      simp at hw
    rw [Function.update_of_ne huv] at hu
    rw [Function.update_of_ne hwv] at hw
    exact ⟨u, w, huv, hwv, hadj, hu, hw⟩
  · rintro ⟨u, w, huv, hwv, hadj, hu, hw⟩
    refine ⟨u, w, hadj, ?_, ?_⟩
    · rwa [Function.update_of_ne huv]
    · rwa [Function.update_of_ne hwv]

end PEqualNP.Outside
