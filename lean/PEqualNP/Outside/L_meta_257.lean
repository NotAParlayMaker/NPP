import Mathlib
import PEqualNP.Defs

noncomputable def L_meta_257_pos {n : ℕ} (i : Fin n) (φ : PEqualNP.MetaComplexity.DMFormula n) : ℕ :=
  φ.rec (fun j c => if j = i ∧ c = true then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q)

noncomputable def L_meta_257_neg {n : ℕ} (i : Fin n) (φ : PEqualNP.MetaComplexity.DMFormula n) : ℕ :=
  φ.rec (fun j c => if j = i ∧ c = false then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q)

noncomputable def L_meta_257_total {n : ℕ} (i : Fin n) (φ : PEqualNP.MetaComplexity.DMFormula n) : ℕ :=
  φ.rec (fun j _ => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q)

theorem L_meta_257_partition {n : ℕ} (i : Fin n) (φ : PEqualNP.MetaComplexity.DMFormula n) :
    L_meta_257_total i φ = L_meta_257_pos i φ + L_meta_257_neg i φ := by
  induction φ with
  | lit j c =>
    cases c <;> by_cases h : j = i <;> simp [L_meta_257_total, L_meta_257_pos, L_meta_257_neg, h]
  | and a b ha hb => simp only [L_meta_257_total, L_meta_257_pos, L_meta_257_neg] at *; omega
  | or a b ha hb => simp only [L_meta_257_total, L_meta_257_pos, L_meta_257_neg] at *; omega

theorem L_meta_257_antitone {n : ℕ} (i : Fin n) (φ : PEqualNP.MetaComplexity.DMFormula n)
    (h : L_meta_257_pos i φ = 0) (x : Fin n → Bool) :
    φ.eval (Function.update x i true) = true → φ.eval (Function.update x i false) = true := by
  induction φ with
  | lit j c =>
    cases c <;> by_cases hj : j = i <;>
      simp_all [L_meta_257_pos, PEqualNP.MetaComplexity.DMFormula.eval, Function.update_of_ne]
  | and a b ha hb =>
    change L_meta_257_pos i a + L_meta_257_pos i b = 0 at h
    have h1 : L_meta_257_pos i a = 0 := by omega
    have h2 : L_meta_257_pos i b = 0 := by omega
    simp only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.and_eq_true]
    exact fun ⟨h3, h4⟩ => ⟨ha h1 h3, hb h2 h4⟩
  | or a b ha hb =>
    change L_meta_257_pos i a + L_meta_257_pos i b = 0 at h
    have h1 : L_meta_257_pos i a = 0 := by omega
    have h2 : L_meta_257_pos i b = 0 := by omega
    simp only [PEqualNP.MetaComplexity.DMFormula.eval, Bool.or_eq_true]
    exact fun h3 => h3.elim (fun h4 => Or.inl (ha h1 h4)) (fun h4 => Or.inr (hb h2 h4))

theorem PEqualNP.Outside.L_meta_257 :
    ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 1 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 := by
  intro n f φ i mono essential computes total
  change L_meta_257_neg i φ = 0
  change L_meta_257_total i φ = 1 at total
  have partition := L_meta_257_partition i φ
  by_contra hn
  have hp : L_meta_257_pos i φ = 0 := by omega
  obtain ⟨x, hx⟩ := essential
  apply hx
  have anti : f (Function.update x i true) = true → f (Function.update x i false) = true := by
    simpa only [computes] using L_meta_257_antitone i φ hp x
  have forward : f (Function.update x i false) = true → f (Function.update x i true) = true := by
    apply mono
    intro j hj
    by_cases hji : j = i
    · subst j; simp
    · simpa [Function.update_of_ne hji] using hj
  cases ht : f (Function.update x i true) <;> cases hf : f (Function.update x i false) <;> simp_all
