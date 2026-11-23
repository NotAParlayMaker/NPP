import Mathlib
import PEqualNP.Defs

-- A de Morgan formula for a monotone function that reads an essential input exactly once
-- reads it as a positive literal.
--
-- The proof: if the single leaf reading `i` is negated, then raising `x i` from `false` to `true`
-- only lowers the value of the formula (the formula is monotone in the values of its leaves),
-- so the value of `f` also does not rise - while monotonicity of `f` in the input says it does
-- not fall. Hence `f` does not depend on `i` at all, contradicting that `i` is essential.

namespace PEqualNP.Outside.L257

open PEqualNP.MetaComplexity

/-- The number of leaves of the formula that read the input `i`. -/
noncomputable def occ {n : ℕ} (i : Fin n) : DMFormula n → ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j _ => if j = i then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q)

/-- The number of leaves of the formula that read the input `i` negated. -/
noncomputable def negOcc {n : ℕ} (i : Fin n) : DMFormula n → ℕ :=
  DMFormula.rec (motive := fun _ => ℕ) (fun j c => if j = i ∧ c = false then 1 else 0)
    (fun _ _ p q => p + q) (fun _ _ p q => p + q)

/-- Negated leaves are leaves: the negated count never exceeds the total count. -/
theorem negOcc_le_occ {n : ℕ} (i : Fin n) : ∀ φ : DMFormula n, negOcc i φ ≤ occ i φ := by
  intro φ
  induction φ with
  | lit j c =>
      change (if j = i ∧ c = false then 1 else 0) ≤ (if j = i then 1 else 0)
      split_ifs <;> omega
  | and a b iha ihb =>
      change negOcc i a + negOcc i b ≤ occ i a + occ i b
      omega
  | or a b iha ihb =>
      change negOcc i a + negOcc i b ≤ occ i a + occ i b
      omega

/-- A formula that never reads `i` gives the same value on two inputs that agree away from `i`. -/
theorem eval_congr {n : ℕ} {i : Fin n} : ∀ φ : DMFormula n, occ i φ = 0 →
    ∀ x y : Fin n → Bool, (∀ j : Fin n, j ≠ i → x j = y j) → φ.eval x = φ.eval y := by
  intro φ
  induction φ with
  | lit j c =>
      intro h x y hxy
      have hji : j ≠ i := by
        intro hji
        have h' : occ i (DMFormula.lit j c) = 1 := by
          change (if j = i then 1 else 0) = 1
          simp [hji]
        omega
      simp only [DMFormula.eval, hxy j hji]
  | and a b iha ihb =>
      intro h x y hxy
      obtain ⟨ha, hb⟩ := Nat.add_eq_zero_iff.mp h
      simp only [DMFormula.eval, iha ha x y hxy, ihb hb x y hxy]
  | or a b iha ihb =>
      intro h x y hxy
      obtain ⟨ha, hb⟩ := Nat.add_eq_zero_iff.mp h
      simp only [DMFormula.eval, iha ha x y hxy, ihb hb x y hxy]

/-- If the single leaf that reads `i` is negated, then raising `x i` to `true` can only lower
the value of the formula. -/
theorem single_neg {n : ℕ} {i : Fin n} : ∀ φ : DMFormula n, occ i φ = 1 → negOcc i φ = 1 →
    ∀ x : Fin n → Bool, φ.eval (Function.update x i true) = true →
      φ.eval (Function.update x i false) = true := by
  intro φ
  induction φ with
  | lit j c =>
      intro h1 h2 x hx
      have hji : j = i := by
        by_contra h
        have h' : occ i (DMFormula.lit j c) = 0 := by
          change (if j = i then 1 else 0) = 0
          simp [h]
        omega
      have hc : c = false := by
        by_contra h
        have h' : negOcc i (DMFormula.lit j c) = 0 := by
          change (if j = i ∧ c = false then 1 else 0) = 0
          simp [hji, h]
        omega
      subst hji
      subst hc
      simp [DMFormula.eval] at hx
  | and a b iha ihb =>
      intro h1 h2 x hx
      have hle1 := negOcc_le_occ i a
      have hle2 := negOcc_le_occ i b
      have h1' : occ i a + occ i b = 1 := h1
      have h2' : negOcc i a + negOcc i b = 1 := h2
      have hcase :
          (occ i a = 1 ∧ occ i b = 0 ∧ negOcc i a = 1 ∧ negOcc i b = 0) ∨
          (occ i a = 0 ∧ occ i b = 1 ∧ negOcc i a = 0 ∧ negOcc i b = 1) := by
        omega
      simp only [DMFormula.eval, Bool.and_eq_true] at hx ⊢
      obtain ⟨hxa, hxb⟩ := hx
      rcases hcase with ⟨ha1, hb0, na1, nb0⟩ | ⟨ha0, hb1, na0, nb1⟩
      · have hb : b.eval (Function.update x i true) = b.eval (Function.update x i false) :=
          eval_congr b hb0 _ _ (by intro j hj; simp [hj])
        exact ⟨iha ha1 na1 x hxa, hb ▸ hxb⟩
      · have ha : a.eval (Function.update x i true) = a.eval (Function.update x i false) :=
          eval_congr a ha0 _ _ (by intro j hj; simp [hj])
        exact ⟨ha ▸ hxa, ihb hb1 nb1 x hxb⟩
  | or a b iha ihb =>
      intro h1 h2 x hx
      have hle1 := negOcc_le_occ i a
      have hle2 := negOcc_le_occ i b
      have h1' : occ i a + occ i b = 1 := h1
      have h2' : negOcc i a + negOcc i b = 1 := h2
      have hcase :
          (occ i a = 1 ∧ occ i b = 0 ∧ negOcc i a = 1 ∧ negOcc i b = 0) ∨
          (occ i a = 0 ∧ occ i b = 1 ∧ negOcc i a = 0 ∧ negOcc i b = 1) := by
        omega
      simp only [DMFormula.eval, Bool.or_eq_true] at hx ⊢
      rcases hcase with ⟨ha1, hb0, na1, nb0⟩ | ⟨ha0, hb1, na0, nb1⟩
      · have hb : b.eval (Function.update x i true) = b.eval (Function.update x i false) :=
          eval_congr b hb0 _ _ (by intro j hj; simp [hj])
        rcases hx with hx1 | hx2
        · exact Or.inl (iha ha1 na1 x hx1)
        · exact Or.inr (hb ▸ hx2)
      · have ha : a.eval (Function.update x i true) = a.eval (Function.update x i false) :=
          eval_congr a ha0 _ _ (by intro j hj; simp [hj])
        rcases hx with hx1 | hx2
        · exact Or.inl (ha ▸ hx1)
        · exact Or.inr (ihb hb1 nb1 x hx2)

end PEqualNP.Outside.L257

theorem PEqualNP.Outside.L_meta_257 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (φ : PEqualNP.MetaComplexity.DMFormula n) (i : Fin n), (∀ x y : Fin n → Bool, (∀ j : Fin n, x j = true → y j = true) → f x = true → f y = true) → (∃ x : Fin n → Bool, f (Function.update x i true) ≠ f (Function.update x i false)) → (∀ x : Fin n → Bool, φ.eval x = f x) → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (_ : Bool) => if j = i then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 1 → PEqualNP.MetaComplexity.DMFormula.rec (motive := fun _ => ℕ) (fun (j : Fin n) (c : Bool) => if j = i ∧ c = false then 1 else 0) (fun _ _ p q => p + q) (fun _ _ p q => p + q) φ = 0 := by
  intro n f φ i hmono hess hcomp
  change PEqualNP.Outside.L257.occ i φ = 1 → PEqualNP.Outside.L257.negOcc i φ = 0
  intro hocc
  by_contra hne
  have hle := PEqualNP.Outside.L257.negOcc_le_occ i φ
  have hpos : 1 ≤ PEqualNP.Outside.L257.negOcc i φ := by omega
  have hone : PEqualNP.Outside.L257.negOcc i φ = 1 := by omega
  obtain ⟨x, hx⟩ := hess
  have hb : φ.eval (Function.update x i true) = f (Function.update x i true) := hcomp _
  have ha : φ.eval (Function.update x i false) = f (Function.update x i false) := hcomp _
  have key1 : f (Function.update x i true) = true → f (Function.update x i false) = true := by
    intro h
    have h' : φ.eval (Function.update x i true) = true := by rw [hb]; exact h
    have := PEqualNP.Outside.L257.single_neg φ hocc hone x h'
    rwa [ha] at this
  have key2 : f (Function.update x i false) = true → f (Function.update x i true) = true := by
    intro h
    refine hmono _ _ ?_ h
    intro j hj
    by_cases hji : j = i
    · subst hji
      simp at hj
    · simpa [hji] using hj
  have heq : f (Function.update x i true) = f (Function.update x i false) := by
    by_cases hbt : f (Function.update x i true) = true
    · rw [hbt]; exact (key1 hbt).symm
    · have hbf : f (Function.update x i true) = false := by simpa using hbt
      by_cases hat : f (Function.update x i false) = true
      · exact absurd (key2 hat) (by rw [hbf]; simp)
      · have haf : f (Function.update x i false) = false := by simpa using hat
        rw [hbf, haf]
  exact hx heq
