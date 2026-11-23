import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_gct_222 : ∀ a b : Fin 4 → ℂ, (∑ j, b j = 0) → a 0 = 0 → (∑ i, a i = 0) → Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + (if i = 0 then b j else if j = 0 then a i else 0)) = 24 := by
  intro a b hb ha0 ha
  rw [Matrix.permanent]
  simp only [Finset.univ_perm_fin_succ (n := 3), Finset.univ_perm_fin_succ (n := 2),
    Finset.univ_perm_fin_succ (n := 1), Finset.univ_perm_fin_succ (n := 0),
    Finset.sum_map, Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_apply_def]
  have hb' : b 0 + b 1 + b 2 + b 3 = 0 := by simpa [Fin.sum_univ_four] using hb
  have ha' : a 0 + a 1 + a 2 + a 3 = 0 := by simpa [Fin.sum_univ_four] using ha
  linear_combination (2 * (3 + a 1 + a 2 + a 3)) * hb' + (6 - 2 * b 0) * (ha' - ha0)
