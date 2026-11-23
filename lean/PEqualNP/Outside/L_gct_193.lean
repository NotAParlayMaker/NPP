import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_gct_193 :
    ∀ c : ℂ, (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, (1 + c * (if (σ i).val = i.val then (1 : ℂ) else if (σ i).val = (i.val + 1) % 4 then Complex.I else if (σ i).val = (i.val + 2) % 4 then -Complex.I else -1))) = 24 := by
  intro c
  simp only [Finset.univ_perm_fin_succ, Finset.sum_map, Equiv.coe_toEmbedding, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Finset.univ_unique, Finset.sum_singleton, Fin.prod_univ_succ, Finset.prod_singleton,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  norm_num [Equiv.swap_apply_def, Fin.ext_iff, Fin.val_succ]
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
  try simp
