import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_180_aux

/-- A primitive cube root of unity. -/
noncomputable def ω : ℂ := -1 / 2 + (Real.sqrt 3 / 2) * Complex.I

lemma hω : ω ^ 2 + ω + 1 = 0 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [ω, pow_two] <;> nlinarith [h3]

/-- The witness: row 0 is any centred row, rows 1 to 3 are one pattern twisted by ω. -/
noncomputable def A (p : Fin 6 → ℂ) : Fin 4 → Fin 5 → ℂ :=
  ![![p 0, p 1, p 2, p 3, -(p 0 + p 1 + p 2 + p 3)],
    ![p 4, -p 4, p 5, -p 5, 0],
    ![ω * p 4, -(ω * p 4), ω ^ 2 * p 5, -(ω ^ 2 * p 5), 0],
    ![ω ^ 2 * p 4, -(ω ^ 2 * p 4), ω * p 5, -(ω * p 5), 0]]

noncomputable def φ : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 5 → ℂ) where
  toFun p x := A p x.1 x.2
  map_add' p q := by
    ext ⟨a, j⟩
    fin_cases a <;> fin_cases j <;> simp [A] <;> ring
  map_smul' c p := by
    ext ⟨a, j⟩
    fin_cases a <;> fin_cases j <;> simp [A] <;> ring

lemma φ_apply (p : Fin 6 → ℂ) (a : Fin 4) (j : Fin 5) : φ p (a, j) = A p a j := rfl

lemma φ_inj : Function.Injective φ := by
  intro p q h
  have e : ∀ x, φ p x = φ q x := fun x => congrFun h x
  have e00 := e (0, 0)
  have e01 := e (0, 1)
  have e02 := e (0, 2)
  have e03 := e (0, 3)
  have e10 := e (1, 0)
  have e12 := e (1, 2)
  simp only [φ_apply, A] at e00 e01 e02 e03 e10 e12
  simp at e00 e01 e02 e03 e10 e12
  funext i
  fin_cases i <;> simpa

lemma P2 (p : Fin 6 → ℂ) :
    (∑ j : Fin 5, ∑ l : Fin 5, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4,
      if a < b then φ p (a, j) * φ p (b, l) else 0) = 0 := by
  simp only [φ_apply, Fin.sum_univ_five, Fin.sum_univ_four]
  simp [A]
  linear_combination (-p 0*p 4 + p 1*p 4 - p 2*p 5 + p 3*p 5 - 2*p 4^2*ω - 2*p 5^2*ω) * hω

lemma P3 (p : Fin 6 → ℂ) :
    (∑ j : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, if j = l ∨ j = m ∨ l = m then 0 else
      ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
        if a < b ∧ b < c then φ p (a, j) * φ p (b, l) * φ p (c, m) else 0) = 0 := by
  simp only [φ_apply, Fin.sum_univ_five, Fin.sum_univ_four]
  simp [A]
  linear_combination (2*p 0*p 4^2*ω + 2*p 1*p 4^2*ω + 2*p 2*p 5^2*ω + 2*p 3*p 5^2*ω) * hω

lemma P4 (p : Fin 6 → ℂ) :
    (∑ j : Fin 5, ∑ l : Fin 5, ∑ m : Fin 5, ∑ n : Fin 5,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
        φ p (0, j) * φ p (1, l) * φ p (2, m) * φ p (3, n)) = 0 := by
  simp only [φ_apply, Fin.sum_univ_five]
  simp [A]
  linear_combination (2*p 0*p 4*p 5^2*ω^2 - 2*p 1*p 4*p 5^2*ω^2 + 2*p 2*p 4^2*p 5*ω^2
    - 2*p 3*p 4^2*p 5*ω^2) * hω

lemma rows (p : Fin 6 → ℂ) (i : Fin 4) : ∑ j, φ p (i, j) = 0 := by
  simp only [φ_apply, Fin.sum_univ_five]
  fin_cases i <;> simp [A]

end PEqualNP.Outside.L_gct_180_aux

open PEqualNP.Outside.L_gct_180_aux in
theorem PEqualNP.Outside.L_gct_180 : ∃ L : Submodule ℂ (Fin 4 × Fin 5 → ℂ), (∀ t ∈ L, (∀ i : Fin 4, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0) = 0 ∧ (∑ j, ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else t (0, j) * t (1, l) * t (2, m) * t (3, n)) = 0) ∧ Module.finrank ℂ L = 6 := by
  refine ⟨LinearMap.range φ, ?_, ?_⟩
  · rintro t ⟨p, rfl⟩
    exact ⟨rows p, P2 p, P3 p, P4 p⟩
  · rw [LinearMap.finrank_range_of_inj φ_inj, Module.finrank_fin_fun]
