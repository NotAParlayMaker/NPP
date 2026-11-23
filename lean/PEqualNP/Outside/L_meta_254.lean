import Mathlib.Combinatorics.SimpleGraph.Basic

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
      by_cases hwv : w = v
      · subst w
        exact False.elim ((G.ne_of_adj huw) rfl)
      · simpa [Function.update, hwv] using hw
    · by_cases hwv : w = v
      · subst w
        left
        refine ⟨u, G.adj_symm huw, ?_⟩
        simpa [Function.update, huv] using hu
      · have hxu : x u = true := by
          simpa [Function.update, huv] using hu
        have hxw : x w = true := by
          simpa [Function.update, hwv] using hw
        by_cases hvu : G.Adj v u
        · exact Or.inl ⟨u, hvu, hxu⟩
        · by_cases hvw : G.Adj v w
          · exact Or.inl ⟨w, hvw, hxw⟩
          · exact Or.inr ⟨u, w, huv, hwv, hvu, hvw, huw, hxu, hxw⟩
  · rintro (⟨u, hvu, hxu⟩ | ⟨u, w, huv, hwv, _hvu, _hvw, huw, hxu, hxw⟩)
    · have hne : u ≠ v := (G.ne_of_adj hvu).symm
      refine ⟨v, u, hvu, ?_, ?_⟩
      · simp
      · simpa [Function.update, hne] using hxu
    · refine ⟨u, w, huw, ?_, ?_⟩
      · simpa [Function.update, huv] using hxu
      · simpa [Function.update, hwv] using hxw
