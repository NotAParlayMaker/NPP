import PEqualNP.Defs

-- L-meta-255. Every leaf of the formula that reads input i is negated, so the formula can
-- only fall when input i is raised from false to true; the function is monotone, so it can
-- only rise. They are the same function, hence it does not depend on input i.

namespace PEqualNP.Outside.LMeta255

open PEqualNP.MetaComplexity

-- With no positive leaf on input i, raising input i never turns the formula on.
theorem raise_keeps_off {n : ℕ} (i : Fin n) (φ : DMFormula n) :
    DMFormula.rec (motive := fun _ => ℕ)
        (fun (j : Fin n) (c : Bool) => if j = i ∧ c = true then 1 else 0)
        (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 →
      ∀ x : Fin n → Bool, φ.eval (Function.update x i true) = true →
        φ.eval (Function.update x i false) = true := by
  induction φ with
  | lit j c =>
    intro h x hx
    by_cases hj : j = i
    · subst hj
      cases c
      · simp [DMFormula.eval] at hx
      · simp at h
    · simp only [DMFormula.eval, Function.update_of_ne hj] at hx ⊢
      exact hx
  | and φ ψ ihφ ihψ =>
    intro h x hx
    obtain ⟨h1, h2⟩ := Nat.add_eq_zero_iff.mp h
    simp only [DMFormula.eval, Bool.and_eq_true] at hx ⊢
    exact ⟨ihφ h1 x hx.1, ihψ h2 x hx.2⟩
  | or φ ψ ihφ ihψ =>
    intro h x hx
    obtain ⟨h1, h2⟩ := Nat.add_eq_zero_iff.mp h
    simp only [DMFormula.eval, Bool.or_eq_true] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (ihφ h1 x hx)
    · exact Or.inr (ihψ h2 x hx)

end PEqualNP.Outside.LMeta255

theorem PEqualNP.Outside.L_meta_255 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = true then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 → ∀ x : Fin n → Bool, f (Function.update x i true) = f (Function.update x i false) := by
  intro n f φ i hmono hφ hcount x
  have up : f (Function.update x i false) = true → f (Function.update x i true) = true := by
    apply hmono
    intro j hj
    by_cases hji : j = i
    · subst hji
      simp
    · rw [Function.update_of_ne hji] at hj ⊢
      exact hj
  have down := PEqualNP.Outside.LMeta255.raise_keeps_off i φ hcount x
  rw [hφ, hφ] at down
  cases hT : f (Function.update x i true) <;> cases hF : f (Function.update x i false)
  · rfl
  · rw [hF] at up
    rw [up rfl] at hT
    exact absurd hT (by decide)
  · rw [hT] at down
    rw [down rfl] at hF
    exact absurd hF (by decide)
  · rfl
