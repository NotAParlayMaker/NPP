import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_146 :
    ∃ x : Fin 6 → ℚ, StrictMono x ∧ (∀ i, 0 < x i) ∧ ∀ i : Fin 5, Polynomial.eval (x i.castSucc) (-Polynomial.X ^ 6 + Polynomial.C (2 * 10 ^ 8) * Polynomial.X ^ 5 - Polynomial.C (10 ^ 16) * Polynomial.X ^ 4 + Polynomial.C (10 ^ 24) * (Polynomial.X - 1) ^ 2 : Polynomial ℚ) * Polynomial.eval (x i.succ) (-Polynomial.X ^ 6 + Polynomial.C (2 * 10 ^ 8) * Polynomial.X ^ 5 - Polynomial.C (10 ^ 16) * Polynomial.X ^ 4 + Polynomial.C (10 ^ 24) * (Polynomial.X - 1) ^ 2 : Polynomial ℚ) < 0 := by
  refine ⟨![1/2, 1, 2, 20000, 10^8, 2*10^8], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> norm_num
  · intro i
    fin_cases i <;> norm_num
  · intro i
    fin_cases i <;> (  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_neg]
      norm_num)
