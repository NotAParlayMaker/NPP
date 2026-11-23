import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_gct_220 : ∀ s : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + s * (![1, Complex.I, -Complex.I, -1] : Fin 4 → ℂ) (j - i)) = 24 := by
  intro s
  rw [Matrix.permanent]
  simp only [Finset.univ_perm_fin_succ (n := 3), Finset.univ_perm_fin_succ (n := 2),
    Finset.univ_perm_fin_succ (n := 1), Finset.univ_perm_fin_succ (n := 0),
    Finset.sum_map, Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def]
  have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination (2 * s ^ 2 * (Complex.I ^ 2 * s ^ 2 - 4 * Complex.I * s ^ 2 + s ^ 2 + 4)) * h2
