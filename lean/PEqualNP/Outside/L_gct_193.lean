import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_193 : ∀ c : ℂ, (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, (1 + c * (if (σ i).val = i.val then (1 : ℂ) else if (σ i).val = (i.val + 1) % 4 then Complex.I else if (σ i).val = (i.val + 2) % 4 then -Complex.I else -1))) = 24 := by
  have sum_perm_succ : ∀ {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ),
      ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
        g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
    intro n g
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  intro c
  rw [sum_perm_succ]
  simp only [sum_perm_succ (n := 2), sum_perm_succ (n := 1), sum_perm_succ (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Fintype.sum_unique]
  simp +decide
  ring_nf
  norm_num [Complex.I_sq, pow_succ]
  ring
