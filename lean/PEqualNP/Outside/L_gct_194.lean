import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.Notation
import PEqualNP.Defs

namespace PEqualNP.Outside.Gct194

abbrev Row := Fin 5
abbrev Rows := Row × Row × Row × Row

def valid (r : Rows) : Prop :=
  r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2.1 ∧ r.1 ≠ r.2.2.2 ∧
    r.2.1 ≠ r.2.2.1 ∧ r.2.1 ≠ r.2.2.2 ∧ r.2.2.1 ≠ r.2.2.2

instance (r : Rows) : Decidable (valid r) := by unfold valid; infer_instance

def rows (f : Fin 4 ↪ Fin 5) : Rows := (f 0, f 1, f 2, f 3)

def atRow (r : Rows) : Fin 4 → Fin 5 := ![r.1, r.2.1, r.2.2.1, r.2.2.2]

private theorem rows_valid (f : Fin 4 ↪ Fin 5) : valid (rows f) := by
  simp [valid, rows, f.injective.eq_iff]

private def embed (r : Rows) (h : valid r) : Fin 4 ↪ Fin 5 where
  toFun := atRow r
  inj' := by
    intro i j
    obtain ⟨h01,h02,h03,h12,h13,h23⟩ := h
    fin_cases i <;> fin_cases j <;> simp_all [atRow, ne_comm]

noncomputable def entry (c d : ℂ) (j : Fin 4) (r : Fin 5) : ℂ :=
  1 + (if r.val = 4 then d * (if j.val = 0 then 1 else if j.val = 1 then -1 else 0)
    else c * (if j.val = r.val then 1 else if j.val = (r.val + 1) % 4 then Complex.I
      else if j.val = (r.val + 2) % 4 then -Complex.I else -1))

noncomputable def term (c d : ℂ) (r : Rows) : ℂ :=
  entry c d 0 r.1 * entry c d 1 r.2.1 * entry c d 2 r.2.2.1 * entry c d 3 r.2.2.2

private theorem expand (c d : ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, entry c d j (f j)) =
      ∑ r : Rows, if valid r then term c d r else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun f _ => rows f)
  · intro f _; simp [rows_valid]
  · intro f _ g _ h
    apply Function.Embedding.ext
    intro i
    have he := congrArg atRow h
    fin_cases i
    · exact congrFun he (0 : Fin 4)
    · exact congrFun he (1 : Fin 4)
    · exact congrFun he (2 : Fin 4)
    · exact congrFun he (3 : Fin 4)
  · intro r hr
    refine ⟨embed r (Finset.mem_filter.mp hr).2, Finset.mem_univ _, rfl⟩
  · intro f _
    simp [Fin.prod_univ_succ, term, rows, mul_assoc]

noncomputable def part (c d : ℂ) (i : Fin 5) : ℂ :=
  ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5,
    if valid (i,j,k,l) then term c d (i,j,k,l) else 0

private theorem part0 (c d : ℂ) : part c d 0 = -2 * Complex.I * c ^ 4 + 4 * c ^ 3 - 2 * Complex.I * c ^ 3 - 2 * c ^ 2 * d - 2 * Complex.I * c ^ 2 * d + 10 * c ^ 2 - 8 * c * d - 2 * Complex.I * c * d + 30 * c - 6 * d + 24 := by
  norm_num [part, Fin.sum_univ_succ, valid, term, entry, Fin.val_succ]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

private theorem part1 (c d : ℂ) : part c d 1 = -2 * Complex.I * c ^ 4 + 2 * c ^ 3 * d - 2 * Complex.I * c ^ 3 * d - 4 * c ^ 3 + 2 * Complex.I * c ^ 3 - 2 * c ^ 2 * d + 2 * Complex.I * c ^ 2 * d + 10 * c ^ 2 + 6 * c * d - 30 * c - 6 * d + 24 := by
  norm_num [part, Fin.sum_univ_succ, valid, term, entry, Fin.val_succ]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

private theorem part2 (c d : ℂ) : part c d 2 = 2 * Complex.I * c ^ 4 - 2 * c ^ 3 + 4 * Complex.I * c ^ 3 + 2 * c ^ 2 * d - 2 * Complex.I * c ^ 2 * d - 10 * c ^ 2 + 2 * c * d + 8 * Complex.I * c * d - 30 * Complex.I * c - 6 * d + 24 := by
  norm_num [part, Fin.sum_univ_succ, valid, term, entry, Fin.val_succ]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

private theorem part3 (c d : ℂ) : part c d 3 = 2 * Complex.I * c ^ 4 - 2 * c ^ 3 * d + 2 * Complex.I * c ^ 3 * d + 2 * c ^ 3 - 4 * Complex.I * c ^ 3 + 2 * c ^ 2 * d + 2 * Complex.I * c ^ 2 * d - 10 * c ^ 2 - 6 * Complex.I * c * d + 30 * Complex.I * c - 6 * d + 24 := by
  norm_num [part, Fin.sum_univ_succ, valid, term, entry, Fin.val_succ]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

private theorem part4 (c d : ℂ) : part c d 4 = 24 * d + 24 := by
  norm_num [part, Fin.sum_univ_succ, valid, term, entry, Fin.val_succ]
  ring_nf
  norm_num [Complex.I_sq]

end PEqualNP.Outside.Gct194

open PEqualNP.Outside.Gct194 in
theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  change (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, entry c d j (f j)) = 120
  rw [expand]
  simp only [Fintype.sum_prod_type]
  change (∑ i : Fin 5, part c d i) = 120
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  change part c d 0 + (part c d 1 + (part c d 2 + (part c d 3 + part c d 4))) = 120
  rw [part0, part1, part2, part3, part4]
  ring
