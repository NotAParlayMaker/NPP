import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Complex.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_gct_193_aux

private def entry (i j : Fin 4) : ℂ :=
  if j.val = i.val then (1 : ℂ)
  else if j.val = (i.val + 1) % 4 then Complex.I
  else if j.val = (i.val + 2) % 4 then -Complex.I
  else -1

private lemma sum_perm4 (f : Equiv.Perm (Fin 4) → ℂ) :
    (∑ σ : Equiv.Perm (Fin 4), f σ) =
      ∑ a : Fin 4, ∑ b : Fin 3, ∑ d : Fin 2,
        f (Equiv.Perm.decomposeFin.symm
          (a, Equiv.Perm.decomposeFin.symm
            (b, Equiv.Perm.decomposeFin.symm (d, (1 : Equiv.Perm (Fin 1)))))) := by
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Fintype.sum_unique]
  rfl

private lemma eval_perm4 (c : ℂ) :
    (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4, (1 + c * entry i (σ i))) = 24 := by
  rw [sum_perm4]
  simp (config := { decide := true }) only [Fin.sum_univ_four, Fin.sum_univ_three,
    Fin.sum_univ_two, Fin.prod_univ_four, entry, ite_true, ite_false]
  ring_nf
  have hi2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have hi3 : Complex.I ^ 3 = -Complex.I := by
    calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
      _ = -Complex.I := by rw [hi2]; ring
  have hi4 : Complex.I ^ 4 = 1 := by
    calc Complex.I ^ 4 = Complex.I ^ 2 * Complex.I ^ 2 := by ring
      _ = 1 := by rw [hi2]; ring
  rw [hi2, hi3, hi4]
  ring

end PEqualNP.Outside.L_gct_193_aux

theorem PEqualNP.Outside.L_gct_193 :
    ∀ c : ℂ, (∑ σ : Equiv.Perm (Fin 4), ∏ i : Fin 4,
      (1 + c * (if (σ i).val = i.val then (1 : ℂ)
        else if (σ i).val = (i.val + 1) % 4 then Complex.I
        else if (σ i).val = (i.val + 2) % 4 then -Complex.I else -1))) = 24 :=
  PEqualNP.Outside.L_gct_193_aux.eval_perm4
