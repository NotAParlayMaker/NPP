import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_148 :
    ∀ i : Fin 9, Polynomial.eval ((![4, 9, 64, 4097/64, 65, 1025, 16380, 16384, 32769, 262144] : Fin 10 → ℚ) i.castSucc) ((Polynomial.C ((1 / 16 : ℚ) ^ 9) * Polynomial.X ^ 7 - Polynomial.C ((1 / 16 : ℚ) ^ 16) * Polynomial.X ^ 9) ^ 3 + (-Polynomial.X + Polynomial.C ((1 / 16 : ℚ) ^ 25) * Polynomial.X ^ 11) ^ 3 + (Polynomial.C (1 / 16 : ℚ) * Polynomial.X ^ 3 - Polynomial.C ((1 / 16 : ℚ) ^ 4) * Polynomial.X ^ 5) ^ 3 : Polynomial ℚ) * Polynomial.eval ((![4, 9, 64, 4097/64, 65, 1025, 16380, 16384, 32769, 262144] : Fin 10 → ℚ) i.succ) ((Polynomial.C ((1 / 16 : ℚ) ^ 9) * Polynomial.X ^ 7 - Polynomial.C ((1 / 16 : ℚ) ^ 16) * Polynomial.X ^ 9) ^ 3 + (-Polynomial.X + Polynomial.C ((1 / 16 : ℚ) ^ 25) * Polynomial.X ^ 11) ^ 3 + (Polynomial.C (1 / 16 : ℚ) * Polynomial.X ^ 3 - Polynomial.C ((1 / 16 : ℚ) ^ 4) * Polynomial.X ^ 5) ^ 3 : Polynomial ℚ) < 0 := by
  intro i
  fin_cases i <;> (  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_neg]
    norm_num)
