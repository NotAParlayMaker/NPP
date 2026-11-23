import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_gct_221 : Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + (![1, Complex.I, -1, -Complex.I] : Fin 4 → ℂ) (j - i)) = 48 := by
  rw [Matrix.permanent]
  simp only [Finset.univ_perm_fin_succ (n := 3), Finset.univ_perm_fin_succ (n := 2),
    Finset.univ_perm_fin_succ (n := 1), Finset.univ_perm_fin_succ (n := 0),
    Finset.sum_map, Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def]
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have h4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
  linear_combination (-8 : ℂ) * h2 + 4 * h4
