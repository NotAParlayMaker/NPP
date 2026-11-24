import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4326

lemma max_indep_iff {α : Type*} (R : α → α → Prop) (f : α → Bool) :
    (∀ u : α, f u = true ↔ ∀ v : α, f v = true → ¬(R u v ∨ R v u)) ↔
      (∀ u v : α, f u = true → f v = true → ¬R u v) ∧
      (∀ u : α, f u = false → ∃ v : α, f v = true ∧ (R u v ∨ R v u)) := by
  constructor
  · intro h
    constructor
    · intro u v hu hv hR
      exact ((h u).mp hu v hv) (Or.inl hR)
    · intro u hu
      have hnt : f u ≠ true := by simp [hu]
      have hnot : ¬ ∀ v : α, f v = true → ¬(R u v ∨ R v u) := fun hall => hnt ((h u).mpr hall)
      push Not at hnot
      exact hnot
  · rintro ⟨h1, h2⟩ u
    constructor
    · intro hu v hv hR
      rcases hR with hR | hR
      · exact h1 u v hu hv hR
      · exact h1 v u hv hu hR
    · intro hall
      cases hfu : f u with
      | true => rfl
      | false =>
        rcases h2 u hfu with ⟨v, hv, hR⟩
        exact False.elim (hall v hv hR)

end PEqualNP.Outside.L_meta_4326

theorem PEqualNP.Outside.L_meta_4326 :
  have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : Fin (42 : ℕ) → Bool), x2 x3 ↔ (∀ (x4 x5 : Fin (42 : ℕ)), x3 x4 = Bool.true → x3 x5 = Bool.true → ¬x1 x4 x5) ∧ ∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.false → ∃ (x6 : Fin (42 : ℕ)), x3 x6 = Bool.true ∧ (x1 x4 x6 ∨ x1 x6 x4) := by
  intro x1 x2 x3
  exact PEqualNP.Outside.L_meta_4326.max_indep_iff x1 x3
