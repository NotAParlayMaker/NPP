import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_257

open PEqualNP.MetaComplexity

noncomputable def cnt {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

noncomputable def neg {n : ℕ} (i : Fin n) (φ : DMFormula n) : ℕ :=
  DMFormula.rec (motive := fun _ => ℕ)
    (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ

lemma cnt_lit {n : ℕ} (i j : Fin n) (c : Bool) :
    cnt i (DMFormula.lit j c) = if j = i then 1 else 0 := rfl
lemma cnt_and {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    cnt i (DMFormula.and φ ψ) = cnt i φ + cnt i ψ := rfl
lemma cnt_or {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    cnt i (DMFormula.or φ ψ) = cnt i φ + cnt i ψ := rfl
lemma neg_lit {n : ℕ} (i j : Fin n) (c : Bool) :
    neg i (DMFormula.lit j c) = if j = i ∧ c = false then 1 else 0 := rfl
lemma neg_and {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    neg i (DMFormula.and φ ψ) = neg i φ + neg i ψ := rfl
lemma neg_or {n : ℕ} (i : Fin n) (φ ψ : DMFormula n) :
    neg i (DMFormula.or φ ψ) = neg i φ + neg i ψ := rfl

lemma neg_le {n : ℕ} (i : Fin n) (φ : DMFormula n) : neg i φ ≤ cnt i φ := by
  induction φ with
  | lit j c =>
    rw [neg_lit, cnt_lit]
    split_ifs <;> simp_all
  | and φ ψ h1 h2 => rw [neg_and, cnt_and]; omega
  | or φ ψ h1 h2 => rw [neg_or, cnt_or]; omega

lemma free {n : ℕ} (i : Fin n) (φ : DMFormula n) (h : cnt i φ = 0) (x : Fin n → Bool)
    (a b : Bool) : φ.eval (Function.update x i a) = φ.eval (Function.update x i b) := by
  induction φ with
  | lit j c =>
    rw [cnt_lit] at h
    have hj : j ≠ i := by
      intro hj; simp [hj] at h
    simp [DMFormula.eval, Function.update_of_ne hj]
  | and φ ψ h1 h2 =>
    rw [cnt_and] at h
    simp only [DMFormula.eval]
    rw [h1 (by omega), h2 (by omega)]
  | or φ ψ h1 h2 =>
    rw [cnt_or] at h
    simp only [DMFormula.eval]
    rw [h1 (by omega), h2 (by omega)]

lemma anti {n : ℕ} (i : Fin n) (φ : DMFormula n) (h1 : cnt i φ = 1) (h2 : neg i φ ≠ 0)
    (x : Fin n → Bool) :
    φ.eval (Function.update x i true) = true → φ.eval (Function.update x i false) = true := by
  induction φ with
  | lit j c =>
    rw [neg_lit] at h2
    have hj : j = i ∧ c = false := by
      by_contra hc; simp [hc] at h2
    obtain ⟨rfl, rfl⟩ := hj
    simp [DMFormula.eval]
  | and φ ψ ih1 ih2 =>
    rw [cnt_and] at h1
    rw [neg_and] at h2
    have l1 := neg_le i φ
    have l2 := neg_le i ψ
    simp only [DMFormula.eval, Bool.and_eq_true]
    rintro ⟨ha, hb⟩
    rcases Nat.eq_zero_or_pos (cnt i φ) with hφ | hφ
    · have hψ : cnt i ψ = 1 := by omega
      refine ⟨?_, ih2 hψ (by omega) hb⟩
      rw [free i φ hφ x false true]; exact ha
    · have hφ1 : cnt i φ = 1 := by omega
      have hψ : cnt i ψ = 0 := by omega
      refine ⟨ih1 hφ1 (by omega) ha, ?_⟩
      rw [free i ψ hψ x false true]; exact hb
  | or φ ψ ih1 ih2 =>
    rw [cnt_or] at h1
    rw [neg_or] at h2
    have l1 := neg_le i φ
    have l2 := neg_le i ψ
    simp only [DMFormula.eval, Bool.or_eq_true]
    rintro (ha | hb)
    · rcases Nat.eq_zero_or_pos (cnt i φ) with hφ | hφ
      · left; rw [free i φ hφ x false true]; exact ha
      · have hφ1 : cnt i φ = 1 := by omega
        left; exact ih1 hφ1 (by omega) ha
    · rcases Nat.eq_zero_or_pos (cnt i ψ) with hψ | hψ
      · right; rw [free i ψ hψ x false true]; exact hb
      · have hψ1 : cnt i ψ = 1 := by omega
        right; exact ih2 hψ1 (by omega) hb

end PEqualNP.Outside.L_meta_257

theorem PEqualNP.Outside.L_meta_257 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 1 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 := by
  intro n f φ i hmono hess hφ h1
  by_contra h2
  obtain ⟨x, hx⟩ := hess
  have a := PEqualNP.Outside.L_meta_257.anti i φ h1 h2 x
  rw [hφ, hφ] at a
  have b : f (Function.update x i false) = true → f (Function.update x i true) = true := by
    apply hmono
    intro j hj
    by_cases hji : j = i
    · subst hji; simp
    · rw [Function.update_of_ne hji] at hj ⊢; exact hj
  apply hx
  cases hT : f (Function.update x i true) <;> cases hF : f (Function.update x i false) <;>
    simp_all
