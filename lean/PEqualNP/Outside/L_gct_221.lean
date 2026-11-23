import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_221_aux

theorem sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n+1)) → ℂ) :
    ∑ σ, f σ = ∑ p : Fin (n+1), ∑ τ : Equiv.Perm (Fin n), f (Equiv.Perm.decomposeFin.symm (p, τ)) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv Equiv.Perm.decomposeFin.symm _ _ (fun _ => rfl)).symm

end PEqualNP.Outside.L_gct_221_aux

open PEqualNP.Outside.L_gct_221_aux in
theorem PEqualNP.Outside.L_gct_221 : Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + (![1, Complex.I, -1, -Complex.I] : Fin 4 → ℂ) (j - i)) = 48 := by
  simp only [Matrix.permanent, sum_perm_succ, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.sum_univ_zero, Finset.univ_unique, Finset.sum_singleton, Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ, Matrix.of_apply]
  simp only [Equiv.swap_apply_def, Fin.succ_inj, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, if_true, if_false, Fin.ext_iff, Fin.val_succ, Fin.val_zero, Fin.isValue]
  norm_num
  ring_nf
  simp [Complex.I_sq]
  ring_nf
