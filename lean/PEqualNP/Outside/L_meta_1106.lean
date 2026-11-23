import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1106 : ∀ (x : List Bool) (i k : ℕ), i < x.length → x.count true = k → ((!(x.getD i false)) = decide (k ≤ (x.eraseIdx i).count true)) := by
  intro x i k hi hk
  have h1 : x = x.take i ++ x[i] :: x.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have h2 : x.eraseIdx i = x.take i ++ x.drop (i + 1) := List.eraseIdx_eq_take_drop_succ x i
  have hget : x.getD i false = x[i] := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [h2, hget]
  rw [h1] at hk
  simp only [List.count_append, List.count_cons] at hk
  cases h : x[i] <;> simp [h] at hk ⊢ <;> omega
