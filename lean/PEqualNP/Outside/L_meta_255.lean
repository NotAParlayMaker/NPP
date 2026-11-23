import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_255_aux

noncomputable def positives {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun j c => if j = i ∧ c = true then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

lemma decreasing {n : ℕ} (i : Fin n) (x : Fin n → Bool) (φ : DMFormula n) :
    positives i φ = 0 →
      φ.eval (Function.update x i true) = true →
      φ.eval (Function.update x i false) = true := by
  induction φ with
  | lit j c =>
    intro hz hv
    by_cases hji : j = i
    · subst j
      cases c with
      | false => simp [DMFormula.eval] at hv
      | true => simp [positives] at hz
    · simpa only [DMFormula.eval, Function.update_of_ne hji] using hv
  | and a b iha ihb =>
    intro hz hv
    change positives i a + positives i b = 0 at hz
    simp only [DMFormula.eval, Bool.and_eq_true] at hv ⊢
    exact ⟨iha (by omega) hv.1, ihb (by omega) hv.2⟩
  | or a b iha ihb =>
    intro hz hv
    change positives i a + positives i b = 0 at hz
    simp only [DMFormula.eval, Bool.or_eq_true] at hv ⊢
    exact hv.elim (fun h => Or.inl (iha (by omega) h)) (fun h => Or.inr (ihb (by omega) h))

end PEqualNP.Outside.L_meta_255_aux

theorem PEqualNP.Outside.L_meta_255 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = true then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 → ∀ x : Fin n → Bool, f (Function.update x i true) = f (Function.update x i false) := by
  intro n f φ i hmono heval hz x
  apply Bool.eq_iff_iff.mpr
  constructor
  · simpa only [heval] using PEqualNP.Outside.L_meta_255_aux.decreasing i x φ hz
  · refine hmono (Function.update x i false) (Function.update x i true) ?_
    intro j hj
    by_cases hji : j = i
    · subst j
      simp
    · simpa only [Function.update_of_ne hji] using hj
