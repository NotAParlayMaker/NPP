import Mathlib
import PEqualNP.Defs

open Finset

/-- Decompose a permutation by its first image, as in the project's PermFour helper. -/
private theorem sum_permutations_193 {n : ℕ} (g : Equiv.Perm (Fin (n + 1)) → ℂ) :
    ∑ σ, g σ = ∑ a : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
      g (Equiv.Perm.decomposeFin.symm (a, τ)) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]

theorem PEqualNP.Outside.L_gct_193 : ∀ c : ℂ, (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, (1 + c * (if (σ i).val = i.val then (1 : ℂ) else if (σ i).val = (i.val + 1) % 4 then Complex.I else if (σ i).val = (i.val + 2) % 4 then -Complex.I else -1))) = 24 := by
  intro c
  rw [sum_permutations_193]
  simp only [sum_permutations_193 (n := 2), sum_permutations_193 (n := 1),
    sum_permutations_193 (n := 0)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.prod_univ_succ,
    Fin.prod_univ_zero, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Fintype.sum_unique]
  simp (config := { decide := true })
  linear_combination (8 * c^2 + (2 * Complex.I^2 - 8 * Complex.I + 2) * c^4) * Complex.I_sq
