import Mathlib.Combinatorics.SimpleGraph.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_254 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) (x : Fin n → Bool), decide (∃ u w : Fin n, G.Adj u w ∧ Function.update x v true u = true ∧ Function.update x v true w = true) = decide ((∃ u : Fin n, G.Adj v u ∧ x u = true) ∨ ∃ u w : Fin n, u ≠ v ∧ w ≠ v ∧ ¬ G.Adj v u ∧ ¬ G.Adj v w ∧ G.Adj u w ∧ x u = true ∧ x w = true) := by
  classical
  intro n G _ v x
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨u, w, huw, hu, hw⟩
    by_cases huv : u = v
    · subst u
      left
      refine ⟨w, huw, ?_⟩
      have hwv : w ≠ v := huw.ne.symm
      simpa [Function.update_of_ne hwv] using hw
    by_cases hwv : w = v
    · subst w
      left
      refine ⟨u, huw.symm, ?_⟩
      simpa [Function.update_of_ne huv] using hu
    have hu0 : x u = true := by simpa [Function.update_of_ne huv] using hu
    have hw0 : x w = true := by simpa [Function.update_of_ne hwv] using hw
    by_cases hvu : G.Adj v u
    · exact Or.inl ⟨u, hvu, hu0⟩
    by_cases hvw : G.Adj v w
    · exact Or.inl ⟨w, hvw, hw0⟩
    exact Or.inr ⟨u, w, huv, hwv, hvu, hvw, huw, hu0, hw0⟩
  · rintro (⟨u, hvu, hu⟩ | ⟨u, w, huv, hwv, _, _, huw, hu, hw⟩)
    · refine ⟨v, u, hvu, by simp, ?_⟩
      have huv : u ≠ v := hvu.ne.symm
      simpa [Function.update_of_ne huv] using hu
    · refine ⟨u, w, huw, ?_, ?_⟩
      · simpa [Function.update_of_ne huv] using hu
      · simpa [Function.update_of_ne hwv] using hw
