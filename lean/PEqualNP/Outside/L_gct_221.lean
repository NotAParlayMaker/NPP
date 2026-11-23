import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_221 : Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + (![1, Complex.I, -1, -Complex.I] : Fin 4 → ℂ) (j - i)) = 48 := by
  have expand {n : ℕ} (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ) :
      A.permanent = ∑ i, A i 0 * (A.submatrix i.succAbove Fin.succ).permanent := by
    unfold Matrix.permanent
    rw [← (Equiv.Perm.decomposeFin' (n := n)).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Finset.mul_sum, Fin.prod_univ_succ, Equiv.Perm.decomposeFin'_symm,
      Equiv.Perm.decomposeFin'Symm_zero, Equiv.Perm.decomposeFin'Symm_succ, Matrix.submatrix_apply]
  have base (A : Matrix (Fin 1) (Fin 1) ℂ) : A.permanent = A 0 0 :=
    Matrix.permanent_eq_elem_of_subsingleton A 0
  simp only [expand (n := 2), expand (n := 1), expand (n := 0), base,
    Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero, Matrix.submatrix_apply,
    Matrix.of_apply]
  apply Complex.ext <;> norm_num [Fin.succAbove, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im]
