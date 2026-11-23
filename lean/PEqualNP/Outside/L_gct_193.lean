import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.L_gct_193 : ∀ c : ℂ, (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, (1 + c * (if (σ i).val = i.val then (1 : ℂ) else if (σ i).val = (i.val + 1) % 4 then Complex.I else if (σ i).val = (i.val + 2) % 4 then -Complex.I else -1))) = 24 := by
  intro c
  have expand {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
      ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
        g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  rw [expand]
  simp only [expand (n := 2), expand (n := 1), expand (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide [Equiv.swap_apply_def]
  ring_nf
  norm_num [show Complex.I ^ 4 = 1 by rw [show 4 = 2 * 2 by decide, pow_mul, Complex.I_sq]; norm_num]
  <;> ring
