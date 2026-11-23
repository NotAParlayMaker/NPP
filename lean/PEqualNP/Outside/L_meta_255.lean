import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_255

open PEqualNP.MetaComplexity

noncomputable def positiveCount {n : ℕ} (φ : DMFormula n) (i : Fin n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun j c => if j = i ∧ c = true then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

lemma eval_antitone {n : ℕ} (φ : DMFormula n) (i : Fin n)
    (hz : positiveCount φ i = 0) (x : Fin n → Bool) :
    φ.eval (Function.update x i true) = true →
      φ.eval (Function.update x i false) = true := by
  induction φ with
  | lit j b =>
    by_cases hji : j = i
    · subst j
      cases b <;> simp_all [positiveCount, DMFormula.eval]
    · simp [DMFormula.eval, Function.update, hji]
  | and φ ψ ihφ ihψ =>
    change positiveCount φ i + positiveCount ψ i = 0 at hz
    have hφ : positiveCount φ i = 0 := by omega
    have hψ : positiveCount ψ i = 0 := by omega
    simp only [DMFormula.eval, Bool.and_eq_true]
    rintro ⟨h₁, h₂⟩
    exact ⟨ihφ hφ h₁, ihψ hψ h₂⟩
  | or φ ψ ihφ ihψ =>
    change positiveCount φ i + positiveCount ψ i = 0 at hz
    have hφ : positiveCount φ i = 0 := by omega
    have hψ : positiveCount ψ i = 0 := by omega
    simp only [DMFormula.eval, Bool.or_eq_true]
    intro h
    exact h.elim (fun h₁ => Or.inl (ihφ hφ h₁)) (fun h₂ => Or.inr (ihψ hψ h₂))

end PEqualNP.Outside.L_meta_255

theorem PEqualNP.Outside.L_meta_255 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = true then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 → ∀ x : Fin n → Bool, f (Function.update x i true) = f (Function.update x i false) := by
  intro n f φ i hmono heval hz x
  have hdown : f (Function.update x i true) = true →
      f (Function.update x i false) = true := by
    rw [← heval, ← heval]
    exact PEqualNP.Outside.L_meta_255.eval_antitone φ i hz x
  have hup : f (Function.update x i false) = true →
      f (Function.update x i true) = true := by
    apply hmono
    intro j hj
    by_cases hji : j = i
    · subst j
      simp
    · simpa [Function.update, hji] using hj
  cases ht : f (Function.update x i true) <;>
    cases hf : f (Function.update x i false) <;> simp_all
