import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private theorem sum_emb_eq {n m : ℕ} (F : (Fin n → Fin m) → ℂ) :
    (∑ f : Fin n ↪ Fin m, F f) =
      ∑ g : Fin n → Fin m, if Function.Injective g then F g else 0 := by
  classical
  rw [← Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin n) (Fin m))
    (fun g => F g.1) (fun f => F f) (fun _ => rfl)]
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun g => by simp) _).symm

private theorem sum_fun_succ {n m : ℕ} (H : (Fin (n + 1) → Fin m) → ℂ) :
    (∑ g : Fin (n + 1) → Fin m, H g) =
      ∑ a : Fin m, ∑ g : Fin n → Fin m, H (Fin.cons a g) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin m) _ _ (fun _ => rfl)).symm

private theorem sum_fun_zero {m : ℕ} (H : (Fin 0 → Fin m) → ℂ) :
    (∑ g : Fin 0 → Fin m, H g) = H Fin.elim0 := by
  rw [Fintype.sum_unique]
  exact congrArg H (Subsingleton.elim _ _)

private theorem inj4 (g : Fin 4 → Fin 5) : Function.Injective g ↔
    (g 0 ≠ g 1 ∧ g 0 ≠ g 2 ∧ g 0 ≠ g 3 ∧ g 1 ≠ g 2 ∧ g 1 ≠ g 3 ∧ g 2 ≠ g 3) := by
  constructor
  · intro h
    exact ⟨h.ne (by decide), h.ne (by decide), h.ne (by decide), h.ne (by decide),
      h.ne (by decide), h.ne (by decide)⟩
  · rintro ⟨h01, h02, h03, h12, h13, h23⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

private theorem cons2 {n : ℕ} {α : Type} (a : α) (g : Fin (n + 2) → α) :
    (Fin.cons a g : Fin (n + 3) → α) 2 = g 1 := rfl

private theorem cons3 {n : ℕ} {α : Type} (a : α) (g : Fin (n + 3) → α) :
    (Fin.cons a g : Fin (n + 4) → α) 3 = g 2 := rfl

private def table (c d : ℂ) : Fin 5 → Fin 4 → ℂ :=
  ![![1 + c, 1 + c * Complex.I, 1 - c * Complex.I, 1 - c],
    ![1 - c, 1 + c, 1 + c * Complex.I, 1 - c * Complex.I],
    ![1 - c * Complex.I, 1 - c, 1 + c, 1 + c * Complex.I],
    ![1 + c * Complex.I, 1 - c * Complex.I, 1 - c, 1 + c],
    ![1 + d, 1 - d, 1, 1]]

theorem L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  have hA : ∀ (i : Fin 5) (j : Fin 4),
      (1 + (if i.val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0)
        else c * (if j.val = i.val then (1 : ℂ) else if j.val = (i.val + 1) % 4 then Complex.I
        else if j.val = (i.val + 2) % 4 then -Complex.I else -1))) = table c d i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [table] <;> ring
  simp only [hA]
  rw [sum_emb_eq (fun g => ∏ j : Fin 4, table c d (g j) j)]
  simp only [inj4, sum_fun_succ, sum_fun_zero, Fin.prod_univ_four]
  simp only [Fin.sum_univ_five, Fin.cons_zero, Fin.cons_one, cons2, cons3]
  simp only [table, ne_eq, Fin.reduceEq, not_false_eq_true, not_true_eq_false, and_true,
    and_false, ite_true, ite_false, add_zero, zero_add, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four]
  ring_nf
  linear_combination (-8 * c ^ 4 * Complex.I) * Complex.I_sq

end PEqualNP.Outside
