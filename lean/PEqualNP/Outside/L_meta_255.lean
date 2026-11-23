import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_255

noncomputable def positiveLeaves {n : ℕ} (i : Fin n) : DMFormula n → ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun j c => if j = i ∧ c = true then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q)

lemma antitoneAt {n : ℕ} (i : Fin n) (x : Fin n → Bool) (φ : DMFormula n)
    (hnone : positiveLeaves i φ = 0) :
    φ.eval (Function.update x i true) = true → φ.eval (Function.update x i false) = true := by
  induction φ with
  | lit j c =>
    by_cases h : j = i
    · subst j
      cases c <;> simp_all [positiveLeaves, DMFormula.eval]
    · simp [DMFormula.eval, Function.update_of_ne h]
  | and p q hp hq =>
    change positiveLeaves i p + positiveLeaves i q = 0 at hnone
    simp only [DMFormula.eval, Bool.and_eq_true]
    rintro ⟨h₁, h₂⟩
    exact ⟨hp (by omega) h₁, hq (by omega) h₂⟩
  | or p q hp hq =>
    change positiveLeaves i p + positiveLeaves i q = 0 at hnone
    simp only [DMFormula.eval, Bool.or_eq_true]
    exact Or.imp (hp (by omega)) (hq (by omega))

end PEqualNP.Outside.L_meta_255

theorem PEqualNP.Outside.L_meta_255 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = true then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 → ∀ x : Fin n → Bool, f (Function.update x i true) = f (Function.update x i false) := by
  intro n f φ i hmono heval hnone x
  apply Bool.eq_iff_iff.mpr
  constructor
  · rw [← heval, ← heval]
    exact PEqualNP.Outside.L_meta_255.antitoneAt i x φ hnone
  · apply hmono
    intro j
    by_cases h : j = i
    · subst j
      simp
    · simp [Function.update_of_ne h]
