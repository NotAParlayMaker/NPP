import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_222

open Equiv

private def fiberCount (i j : Fin 4) : ℕ :=
  (Finset.univ.filter (fun p : Perm (Fin 4) => p 0 = i ∧ p.symm 0 = j)).card

private theorem fiberValues : ∀ (i j : Fin 4),
    fiberCount i j = if i = 0 ∧ j = 0 then 6 else if i = 0 ∨ j = 0 then 0 else 2 := by
  decide

private theorem groupTerms (f : Fin 4 → Fin 4 → ℂ) :
    (∑ p : Perm (Fin 4), f (p 0) (p.symm 0)) =
      ∑ i : Fin 4, ∑ j : Fin 4, (fiberCount i j : ℂ) * f i j := by
  calc
    _ = ∑ p : Perm (Fin 4), ∑ i : Fin 4, ∑ j : Fin 4,
          if p 0 = i ∧ p.symm 0 = j then f i j else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rfl

private theorem factorTerm (a b : Fin 4 → ℂ) (ha0 : a 0 = 0) (p : Perm (Fin 4)) :
    (∏ j : Fin 4, ((1 : ℂ) + (if p j = 0 then b j else if j = 0 then a (p j) else 0))) =
      (1 + a (p 0)) * (1 + b (p.symm 0)) := by
  have hfactor (j : Fin 4) :
      (1 : ℂ) + (if p j = 0 then b j else if j = 0 then a (p j) else 0) =
        (if j = 0 then 1 + a (p 0) else 1) * (if p j = 0 then 1 + b j else 1) := by
    by_cases hj : j = 0
    · subst j
      by_cases hp : p 0 = 0 <;> simp [hp, ha0]
    · by_cases hp : p j = 0 <;> simp [hj, hp]
  have hr : (∏ j : Fin 4, if j = 0 then 1 + a (p 0) else 1) = 1 + a (p 0) := by
    simp
  have heq (j : Fin 4) : p j = 0 ↔ j = p.symm 0 := by
    constructor
    · intro h
      rw [← h, Equiv.symm_apply_apply]
    · intro h
      rw [h, Equiv.apply_symm_apply]
  have hc : (∏ j : Fin 4, if p j = 0 then 1 + b j else 1) =
      1 + b (p.symm 0) := by
    simp [heq]
  calc
    _ = ∏ j : Fin 4, ((if j = 0 then 1 + a (p 0) else 1) *
          (if p j = 0 then 1 + b j else 1)) := Finset.prod_congr rfl fun j _ => hfactor j
    _ = _ := by rw [Finset.prod_mul_distrib, hr, hc]

end PEqualNP.Outside.L_gct_222

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_gct_222 : ∀ a b : Fin 4 → ℂ, (∑ j, b j = 0) → a 0 = 0 → (∑ i, a i = 0) → Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1 : ℂ) + (if i = 0 then b j else if j = 0 then a i else 0)) = 24 := by
  open PEqualNP.Outside.L_gct_222 in
  intro a b hb ha0 ha
  simp only [Matrix.permanent, Matrix.of_apply]
  calc
    _ = ∑ p : Equiv.Perm (Fin 4), ((1 + a (p 0)) * (1 + b (p.symm 0))) :=
      Finset.sum_congr rfl fun p _ => factorTerm a b ha0 p
    _ = 24 := ?_
  rw [groupTerms (fun i j => (1 + a i) * (1 + b j))]
  simp only [fiberValues, Fin.sum_univ_four] at ha hb ⊢
  norm_num [ha0] at ha ⊢
  linear_combination 6 * hb + (2 * (3 + b 1 + b 2 + b 3)) * ha
